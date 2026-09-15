//! Packed persistent layers with exact paired weights and deterministic merging.
//!
//! Sectors remain sequential. Every layer transition emits labelled
//! contributions from direct word surgery into key-hash buckets, then reduces
//! each bucket by sorting and additive merging, so the layer order depends only
//! on the keys, never on the worker count. Weights start as checked u64; a
//! layer whose total mass could overflow the next transition is widened in
//! place to u128 and then BigUint, so no work is repeated. Certificate
//! visitors decode rows through the packed codec into reference order. Wide
//! sectors fall back to the reference implementation. The worker count is
//! bounded by the bucket count, since a worker only ever holds one bucket.

use super::packed::CAPACITY;
use super::reference::{self, Counts, Row as ReferenceRow, Weights};
use super::word::{Plan, Word};
use super::{InputError, Parameters, Sector, Stage};
use crate::algorithms::{EvalError, Evaluator, check_order};
use crate::problem::Problem;
use num_bigint::BigUint;
use std::convert::Infallible;
use std::fmt;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex};

#[derive(Debug, Clone, Copy)]
pub struct Config {
    pub threads: usize,
}

/// The largest effective worker count: one worker per bucket. Requests above
/// it are reduced to it; a request of zero means one worker.
pub const MAX_WORKERS: usize = BUCKETS;

impl Config {
    /// The worker count a run with this configuration actually uses.
    pub fn effective_threads(self) -> usize {
        self.threads.clamp(1, MAX_WORKERS)
    }
}

impl Default for Config {
    fn default() -> Self {
        Self { threads: 1 }
    }
}

/// Exact nonnegative weight arithmetic. Fixed-width tiers report their
/// capacity so that a layer can be widened before any sum could overflow.
trait Weight: Clone + Default + Send + Sync + PartialEq + fmt::Debug {
    /// The largest representable value, or None for arbitrary precision.
    const MAX: Option<u128>;
    fn one() -> Self;
    /// False when the exact sum does not fit this representation.
    fn add(&mut self, other: &Self) -> bool;
    /// Only called on fixed-width tiers, whose values always fit.
    fn to_u128(&self) -> u128;
    fn from_u128(value: u128) -> Self;
    fn into_big(self) -> BigUint;
}

macro_rules! fixed_width_weight {
    ($($t:ty),*) => {$(
        impl Weight for $t {
            const MAX: Option<u128> = Some(<$t>::MAX as u128);
            fn one() -> Self {
                1
            }
            fn add(&mut self, other: &Self) -> bool {
                match self.checked_add(*other) {
                    Some(sum) => {
                        *self = sum;
                        true
                    }
                    None => false,
                }
            }
            fn to_u128(&self) -> u128 {
                u128::from(*self)
            }
            fn from_u128(value: u128) -> Self {
                <$t>::try_from(value).expect("widened weights fit the next tier")
            }
            fn into_big(self) -> BigUint {
                BigUint::from(self)
            }
        }
    )*};
}

fixed_width_weight!(u64, u128);
#[cfg(test)]
fixed_width_weight!(u8, u16);

impl Weight for BigUint {
    const MAX: Option<u128> = None;
    fn one() -> Self {
        1u32.into()
    }
    fn add(&mut self, other: &Self) -> bool {
        *self += other;
        true
    }
    fn to_u128(&self) -> u128 {
        u128::try_from(self).expect("only fixed-width tiers are measured")
    }
    fn from_u128(value: u128) -> Self {
        value.into()
    }
    fn into_big(self) -> BigUint {
        self
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Row<W> {
    key: Word,
    ordinary: W,
    lower_returns: W,
}

impl<W: Weight> Row<W> {
    fn widen<V: Weight>(self) -> Row<V> {
        Row {
            key: self.key,
            ordinary: V::from_u128(self.ordinary.to_u128()),
            lower_returns: V::from_u128(self.lower_returns.to_u128()),
        }
    }
}

const BUCKET_BITS: u32 = 8;
const BUCKETS: usize = 1 << BUCKET_BITS;
/// Layers at least this large run on the whole worker set; tests lower it
/// to exercise the worker path on small whole runs.
const PARALLEL_ROWS: usize = 4096;

fn bucket(key: Word) -> usize {
    (key.hash() >> (u64::BITS - BUCKET_BITS)) as usize
}

/// A layer is stored bucket by bucket; each bucket is sorted by key.
type Layer<W> = Vec<Mutex<Vec<Row<W>>>>;

fn empty_layer<W>() -> Layer<W> {
    (0..BUCKETS).map(|_| Mutex::new(Vec::new())).collect()
}

/// The layer and one bucket set per worker, retained across sectors so that
/// their capacities are not repeatedly returned to and faulted back from the
/// operating system.
struct Buffers<W> {
    layer: Layer<W>,
    pieces: Vec<Layer<W>>,
}

impl<W> Buffers<W> {
    fn new(threads: usize) -> Self {
        Self {
            layer: empty_layer(),
            pieces: (0..threads).map(|_| empty_layer()).collect(),
        }
    }

    fn clear(&mut self) {
        for bucket in self.layer.iter().chain(self.pieces.iter().flatten()) {
            bucket.lock().unwrap().clear();
        }
    }
}

/// Append the labelled successors of one row to the buckets of their keys.
/// The last accepted label takes ownership of the row's weights.
fn emit<W: Weight>(
    plan: &Plan,
    row: &mut Row<W>,
    buckets: &mut [impl std::ops::DerefMut<Target = Vec<Row<W>>>],
) {
    let targets = plan.successors(row.key);
    let last = targets.iter().rposition(Option::is_some);
    for (i, target) in targets.into_iter().enumerate() {
        let Some((key, increment)) = target else {
            continue;
        };
        let (ordinary, mut lower_returns) = if Some(i) == last {
            (
                std::mem::take(&mut row.ordinary),
                std::mem::take(&mut row.lower_returns),
            )
        } else {
            (row.ordinary.clone(), row.lower_returns.clone())
        };
        assert!(
            !increment || lower_returns.add(&ordinary),
            "the layer mass bound excludes fixed-width overflow"
        );
        buckets[bucket(key)].push(Row {
            key,
            ordinary,
            lower_returns,
        });
    }
}

/// Plans of one stage, built on first use per counter block and kept sorted
/// by block. Sorted buckets group rows by block, so the previous plan
/// usually applies and a binary search covers the rest.
struct Plans {
    sector: Sector,
    stage: Stage,
    plans: Vec<Plan>,
    last: usize,
}

impl Plans {
    fn new(sector: Sector, stage: Stage) -> Self {
        Self {
            sector,
            stage,
            plans: Vec::new(),
            last: 0,
        }
    }

    fn get(&mut self, key: Word) -> &Plan {
        let block = key.block();
        if self
            .plans
            .get(self.last)
            .is_none_or(|plan| plan.block() != block)
        {
            self.last = match self.plans.binary_search_by_key(&block, Plan::block) {
                Ok(index) => index,
                Err(index) => {
                    self.plans
                        .insert(index, Plan::new(self.sector, self.stage, key.counters()));
                    index
                }
            };
        }
        &self.plans[self.last]
    }
}

/// Combine equal keys through a bounded open-addressing index so that only
/// unique rows are sorted. Hash equality never replaces full key equality;
/// slots hold 1-based row positions. Rows beyond the u32 range keep the plain
/// sort and merge.
fn combine<W: Weight>(rows: &mut Vec<Row<W>>, slots: &mut Vec<u32>) {
    let Some(capacity) = rows
        .len()
        .checked_mul(2)
        .and_then(usize::checked_next_power_of_two)
        .filter(|_| rows.len() >= 64 && rows.len() < u32::MAX as usize)
    else {
        return;
    };
    slots.clear();
    slots.resize(capacity, 0);
    let mask = capacity - 1;
    let mut unique = 0;
    for i in 0..rows.len() {
        let key = rows[i].key;
        let mut slot = (key.hash() >> 7) as usize & mask;
        loop {
            let index = slots[slot] as usize;
            if index == 0 {
                slots[slot] = u32::try_from(unique + 1).expect("bounded row index");
                rows.swap(unique, i);
                unique += 1;
                break;
            }
            if rows[index - 1].key == key {
                let (earlier, later) = rows.split_at_mut(i);
                let target = &mut earlier[index - 1];
                let fits = target.ordinary.add(&later[0].ordinary);
                let fits = target.lower_returns.add(&later[0].lower_returns) && fits;
                assert!(fits, "the layer mass bound excludes fixed-width overflow");
                break;
            }
            slot = (slot + 1) & mask;
        }
    }
    rows.truncate(unique);
}

/// Combine and sort one bucket by key, merging any remaining equal keys in
/// place. Equal labelled successors are contributions, never distinct keys.
/// Returns the bucket's saturated ordinary and lower-return mass on
/// fixed-width tiers.
fn reduce<W: Weight>(rows: &mut Vec<Row<W>>, slots: &mut Vec<u32>) -> [u128; 2] {
    combine(rows, slots);
    rows.sort_unstable_by_key(|row| row.key);
    rows.dedup_by(|later, earlier| {
        if later.key != earlier.key {
            return false;
        }
        let fits = earlier.ordinary.add(&later.ordinary);
        let fits = earlier.lower_returns.add(&later.lower_returns) && fits;
        assert!(fits, "the layer mass bound excludes fixed-width overflow");
        true
    });
    if W::MAX.is_none() {
        return [0; 2];
    }
    rows.iter().fold([0; 2], |[c, e], row| {
        [
            c.saturating_add(row.ordinary.to_u128()),
            e.saturating_add(row.lower_returns.to_u128()),
        ]
    })
}

/// A reusable rendezvous that spins briefly before parking. Layers are
/// short, so pure sleeping would lose most of a small layer to wake-up
/// latency, while pure spinning starves working threads.
struct Barrier {
    parties: usize,
    arrived: AtomicUsize,
    generation: AtomicUsize,
    lock: Mutex<()>,
    wake: Condvar,
}

impl Barrier {
    const SPINS: u32 = 2000;

    fn new(parties: usize) -> Self {
        Self {
            parties,
            arrived: AtomicUsize::new(0),
            generation: AtomicUsize::new(0),
            lock: Mutex::new(()),
            wake: Condvar::new(),
        }
    }

    fn wait(&self) {
        if self.parties == 1 {
            return;
        }
        let generation = self.generation.load(Ordering::Acquire);
        if self.arrived.fetch_add(1, Ordering::AcqRel) + 1 == self.parties {
            self.arrived.store(0, Ordering::Release);
            let _guard = self.lock.lock().unwrap();
            self.generation.store(generation + 1, Ordering::Release);
            self.wake.notify_all();
            return;
        }
        for _ in 0..Self::SPINS {
            if self.generation.load(Ordering::Acquire) != generation {
                return;
            }
            std::hint::spin_loop();
        }
        let mut guard = self.lock.lock().unwrap();
        while self.generation.load(Ordering::Acquire) == generation {
            guard = self.wake.wait(guard).unwrap();
        }
    }
}

/// Shared state of one phase of a sector's layer loop.
struct Shared<'a, W> {
    sector: Sector,
    layer: &'a Layer<W>,
    /// One bucket set per worker, holding its emitted rows until reduction.
    pieces: &'a [Layer<W>],
    barrier: Barrier,
    /// Raised by a failing visitor; every worker leaves at the next rendezvous.
    stop: &'a AtomicBool,
    /// Bucket claims for emission and reduction; layer `k` claims the range
    /// `k * BUCKETS..(k + 1) * BUCKETS` of each counter.
    claims: [AtomicUsize; 2],
    /// Reduced row counts and saturated masses of the even and odd layers.
    live: [AtomicUsize; 2],
    mass: [Mutex<[u128; 2]>; 2],
    /// Whether the leader needs the layer to itself between transitions.
    exclusive: bool,
    /// The configured worker count; a one-worker run never switches phases.
    threads: usize,
    /// Layer size at which the whole worker set takes over.
    parallel_rows: usize,
}

impl<'a, W> Shared<'a, W> {
    fn new(
        sector: Sector,
        layer: &'a Layer<W>,
        pieces: &'a [Layer<W>],
        stop: &'a AtomicBool,
        exclusive: bool,
        threads: usize,
        parallel_rows: usize,
    ) -> Self {
        Self {
            sector,
            layer,
            pieces,
            barrier: Barrier::new(pieces.len()),
            stop,
            claims: [const { AtomicUsize::new(0) }; 2],
            live: [const { AtomicUsize::new(0) }; 2],
            mass: [const { Mutex::new([0; 2]) }; 2],
            exclusive,
            threads,
            parallel_rows,
        }
    }
}

/// Claim the next unclaimed bucket of this phase, never one of the next.
fn claim(counter: &AtomicUsize, k: usize) -> Option<usize> {
    let end = (k + 1) * BUCKETS;
    let mut current = counter.load(Ordering::Acquire);
    while current < end {
        match counter.compare_exchange_weak(
            current,
            current + 1,
            Ordering::AcqRel,
            Ordering::Acquire,
        ) {
            Ok(_) => return Some(current - k * BUCKETS),
            Err(seen) => current = seen,
        }
    }
    None
}

/// Layer transition `k` as seen by worker `id`. Workers claim buckets
/// dynamically: each claimed bucket's rows are emitted into the worker's own
/// pieces; after a rendezvous, each claimed bucket gathers every worker's
/// pieces and is reduced. Bucket contents depend only on the keys, and no
/// rows are copied serially.
fn step<W: Weight>(
    shared: &Shared<'_, W>,
    id: usize,
    k: usize,
    stage: Stage,
    spare: &mut Vec<Vec<Row<W>>>,
    slots: &mut Vec<u32>,
) {
    let Shared {
        sector,
        layer,
        pieces,
        barrier,
        claims,
        live,
        mass,
        ..
    } = shared;
    if id == 0 {
        // Nobody reads this parity until after the next rendezvous.
        live[k % 2].store(0, Ordering::Release);
        *mass[k % 2].lock().unwrap() = [0; 2];
    }
    let mut buckets: Vec<_> = pieces[id].iter().map(|b| b.lock().unwrap()).collect();
    let mut plans = Plans::new(*sector, stage);
    while let Some(b) = claim(&claims[0], k) {
        let mut rows = std::mem::take(&mut *layer[b].lock().unwrap());
        for row in rows.iter_mut() {
            emit(plans.get(row.key), row, &mut buckets);
        }
        rows.clear();
        spare.push(rows);
    }
    drop(buckets);
    barrier.wait();
    let mut total = [0u128; 2];
    let mut count = 0;
    while let Some(b) = claim(&claims[1], k) {
        let mut rows = spare.pop().unwrap_or_default();
        for piece in pieces.iter() {
            rows.append(&mut piece[b].lock().unwrap());
        }
        let [c, e] = reduce(&mut rows, slots);
        total = [total[0].saturating_add(c), total[1].saturating_add(e)];
        count += rows.len();
        *layer[b].lock().unwrap() = rows;
    }
    live[k % 2].fetch_add(count, Ordering::AcqRel);
    let mut mass = mass[k % 2].lock().unwrap();
    *mass = [
        mass[0].saturating_add(total[0]),
        mass[1].saturating_add(total[1]),
    ];
    drop(mass);
    barrier.wait();
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Outcome {
    /// The terminal layer is complete.
    Done,
    /// The layer size crossed the parallel threshold; switch worker sets.
    Switch,
    /// The next transition might not fit this weight tier.
    Widen,
    /// The visitor asked to stop.
    Stopped,
}

/// The layer loop run by every worker of one phase. In exclusive mode the
/// leader (id 0) runs `between` after each transition, which may visit the
/// layer and returns false to stop, while the others wait. Every worker
/// returns the same outcome, leaving `stage` at the current layer.
fn work<W: Weight>(
    shared: &Shared<'_, W>,
    id: usize,
    stage: &mut Stage,
    between: &mut dyn FnMut(Stage) -> bool,
) -> Outcome {
    let parallel = shared.pieces.len() > 1;
    let mut spare = Vec::new();
    let mut slots = Vec::new();
    for k in 0.. {
        let Some(side) = shared.sector.side_at(stage.tick) else {
            return Outcome::Done;
        };
        step(shared, id, k, *stage, &mut spare, &mut slots);
        *stage = stage.next(side);
        if shared.exclusive {
            if id == 0 && !between(*stage) {
                shared.stop.store(true, Ordering::Release);
            }
            shared.barrier.wait();
        }
        if shared.stop.load(Ordering::Acquire) {
            return Outcome::Stopped;
        }
        // Every next-layer weight is a sum of at most four contributions per
        // row, so four times the layer mass bounds it, including increments.
        let [c, e] = *shared.mass[k % 2].lock().unwrap();
        let fits = match W::MAX {
            Some(max) => c
                .checked_add(e)
                .and_then(|sum| sum.checked_mul(4))
                .is_some_and(|bound| bound <= max),
            None => true,
        };
        if !fits {
            return Outcome::Widen;
        }
        let rows = shared.live[k % 2].load(Ordering::Acquire);
        if shared.threads > 1
            && (rows >= shared.parallel_rows) != parallel
            && shared.sector.side_at(stage.tick).is_some()
        {
            return Outcome::Switch;
        }
    }
    unreachable!("the stage schedule is finite")
}

type Visitor<'a, E> = dyn FnMut(Sector, Stage, &[ReferenceRow]) -> Result<(), E> + 'a;

fn visit_layer<W: Weight, E>(
    sector: Sector,
    stage: Stage,
    layer: &Layer<W>,
    visitor: &mut Option<&mut Visitor<'_, E>>,
) -> Result<(), E> {
    if let Some(visit) = visitor {
        let mut decoded: Vec<_> = layer
            .iter()
            .flat_map(|bucket| {
                bucket
                    .lock()
                    .unwrap()
                    .iter()
                    .map(|row| ReferenceRow {
                        key: row
                            .key
                            .packed()
                            .decode(sector, stage)
                            .expect("reachable packed key"),
                        weights: Weights {
                            ordinary: row.ordinary.clone().into_big(),
                            lower_returns: row.lower_returns.clone().into_big(),
                        },
                    })
                    .collect::<Vec<_>>()
            })
            .collect();
        // Certificate order is the reference full mate-list order.
        decoded.sort_unstable_by(|a, b| a.key.cmp(&b.key));
        visit(sector, stage, &decoded)?;
    }
    Ok(())
}

/// A layer whose next transition needs a wider weight tier.
struct Widen<W> {
    stage: Stage,
    rows: Vec<Row<W>>,
}

impl<W: Weight> Widen<W> {
    fn into<V: Weight>(self) -> Widen<V> {
        Widen {
            stage: self.stage,
            rows: self.rows.into_iter().map(Row::widen).collect(),
        }
    }
}

/// Scan one sector on one weight tier, from its seed or from a widened layer
/// that the visitor has already seen. One worker handles small layers and the
/// whole worker set large ones; the outer result is the visitor's.
fn scan_with<W: Weight, E>(
    sector: Sector,
    buffers: &mut Buffers<W>,
    visitor: &mut Option<&mut Visitor<'_, E>>,
    resume: Option<Widen<W>>,
    parallel_rows: usize,
) -> Result<Result<Counts, Widen<W>>, E> {
    buffers.clear();
    let Buffers { layer, pieces } = &*buffers;
    let threads = pieces.len();
    let mut stage = sector.initial_stage();
    let mut rows = 1;
    match resume {
        Some(widen) => {
            stage = widen.stage;
            rows = widen.rows.len();
            for row in widen.rows {
                layer[bucket(row.key)].lock().unwrap().push(row);
            }
        }
        None => {
            layer[bucket(Word::empty())].lock().unwrap().push(Row {
                key: Word::empty(),
                ordinary: W::one(),
                lower_returns: W::default(),
            });
            visit_layer(sector, stage, layer, visitor)?;
        }
    }
    let visiting = visitor.is_some();
    let stop = AtomicBool::new(false);
    let mut failure = None;
    let mut between = |stage: Stage| match visit_layer(sector, stage, layer, visitor) {
        Ok(()) => true,
        Err(error) => {
            failure = Some(error);
            false
        }
    };
    let mut outcome = Outcome::Switch;
    while outcome == Outcome::Switch {
        let parallel = threads > 1 && rows >= parallel_rows;
        #[cfg(test)]
        if parallel {
            tests::PARALLEL_PHASES.with(|count| count.set(count.get() + 1));
        }
        let set = if parallel { &pieces[..] } else { &pieces[..1] };
        let shared = Shared::new(
            sector,
            layer,
            set,
            &stop,
            visiting || !parallel,
            threads,
            parallel_rows,
        );
        let start = stage;
        outcome = std::thread::scope(|scope| {
            let handles: Vec<_> = (1..set.len())
                .map(|id| {
                    let shared = &shared;
                    scope.spawn(move || work(shared, id, &mut { start }, &mut |_| true))
                })
                .collect();
            let outcome = work(&shared, 0, &mut stage, &mut between);
            for handle in handles {
                assert_eq!(
                    handle.join().expect("First-Crossing worker panicked"),
                    outcome
                );
            }
            outcome
        });
        let k = stage.tick - start.tick;
        rows = shared.live[(k + 1) % 2].load(Ordering::Acquire);
    }
    if let Some(error) = failure {
        return Err(error);
    }
    // Drain in place so that the retained buckets keep their capacity.
    let drained = || {
        layer
            .iter()
            .flat_map(|b| b.lock().unwrap().drain(..).collect::<Vec<_>>())
            .collect::<Vec<_>>()
    };
    match outcome {
        Outcome::Widen => {
            return Ok(Err(Widen {
                stage,
                rows: drained(),
            }));
        }
        Outcome::Done => {}
        Outcome::Switch | Outcome::Stopped => unreachable!("handled above"),
    }
    let mut counts = Counts::default();
    for row in drained() {
        assert_eq!(
            row.key.counters(),
            sector.budgets(),
            "terminal down budgets"
        );
        assert!(
            row.key
                .packed()
                .decode(sector, stage)
                .expect("terminal packed key")
                .mate
                .is_empty(),
            "terminal frontier is empty"
        );
        counts.closed += row.ordinary.into_big();
        counts.open_even += row.lower_returns.into_big();
    }
    if sector.terminal_bonus() {
        counts.open_even += &counts.closed;
    }
    Ok(Ok(counts))
}

/// Per-run state: the bounded worker count and the retained narrow buffers.
struct Engine {
    threads: usize,
    parallel_rows: usize,
    narrow: Buffers<u64>,
}

impl Engine {
    fn new(config: Config, parallel_rows: usize) -> Self {
        let threads = config.effective_threads();
        Self {
            threads,
            parallel_rows,
            narrow: Buffers::new(threads),
        }
    }

    fn scan<E>(
        &mut self,
        sector: Sector,
        mut visitor: Option<&mut Visitor<'_, E>>,
    ) -> Result<Counts, E> {
        let packable = sector.port_bound() <= CAPACITY
            && sector.budgets().iter().all(|&b| b <= usize::from(u16::MAX));
        if !packable {
            return reference::scan(sector, |sector, stage, rows| match &mut visitor {
                Some(visit) => visit(sector, stage, rows),
                None => Ok(()),
            });
        }
        let (threads, rows) = (self.threads, self.parallel_rows);
        let widen = match scan_with(sector, &mut self.narrow, &mut visitor, None, rows)? {
            Ok(counts) => return Ok(counts),
            Err(widen) => widen.into::<u128>(),
        };
        let mut buffers = Buffers::new(threads);
        let widen = match scan_with(sector, &mut buffers, &mut visitor, Some(widen), rows)? {
            Ok(counts) => return Ok(counts),
            Err(widen) => widen.into::<BigUint>(),
        };
        let mut buffers = Buffers::new(threads);
        Ok(
            scan_with(sector, &mut buffers, &mut visitor, Some(widen), rows)?
                .unwrap_or_else(|_| unreachable!("BigUint layers never widen")),
        )
    }
}

/// `MIN_ROWS` is the parallel cutoff; production uses `PARALLEL_ROWS`.
fn run<const MIN_ROWS: usize, E>(
    parameters: Parameters,
    config: Config,
    mut visitor: Option<&mut Visitor<'_, E>>,
) -> Result<Counts, E> {
    if parameters.order() == 0 {
        return Ok(Counts {
            closed: BigUint::default(),
            open_even: 1u32.into(),
        });
    }
    let mut engine = Engine::new(config, MIN_ROWS);
    let mut counts = Counts::default();
    for sector in parameters.sectors() {
        let part = match &mut visitor {
            Some(visit) => engine.scan(sector, Some(*visit))?,
            None => engine.scan(sector, None)?,
        };
        counts.closed += part.closed;
        counts.open_even += part.open_even;
    }
    Ok(counts)
}

pub fn for_each_layer_with_config<E>(
    parameters: Parameters,
    config: Config,
    mut visit: impl FnMut(Sector, Stage, &[ReferenceRow]) -> Result<(), E>,
) -> Result<Counts, E> {
    run::<PARALLEL_ROWS, _>(parameters, config, Some(&mut visit))
}

#[cfg(test)]
pub fn for_each_layer<E>(
    parameters: Parameters,
    visit: impl FnMut(Sector, Stage, &[ReferenceRow]) -> Result<(), E>,
) -> Result<Counts, E> {
    for_each_layer_with_config(parameters, Config::default(), visit)
}

#[cfg(test)]
pub fn evaluate_with_threshold(
    n: usize,
    threshold: Option<usize>,
    config: Config,
) -> Result<Counts, InputError> {
    let parameters = Parameters::new(n, threshold)?;
    Ok(run::<PARALLEL_ROWS, Infallible>(parameters, config, None).unwrap())
}

pub fn evaluate(n: usize, config: Config) -> Result<Counts, InputError> {
    let parameters = Parameters::new(n, None)?;
    Ok(run::<PARALLEL_ROWS, Infallible>(parameters, config, None).unwrap())
}

pub struct FirstCrossingOptimized {
    pub config: Config,
}

impl Evaluator for FirstCrossingOptimized {
    fn max_order(&self, problem: Problem) -> usize {
        reference::FirstCrossing.max_order(problem)
    }

    fn count(&self, problem: Problem, n: usize) -> Result<Option<BigUint>, EvalError> {
        check_order(n, self.max_order(problem))?;
        let rank = if problem == Problem::Open {
            n.div_ceil(2)
        } else {
            n
        };
        let counts = evaluate(rank, self.config).map_err(EvalError::FirstCrossing)?;
        Ok(Some(if problem == Problem::Open && n.is_multiple_of(2) {
            counts.open_even
        } else {
            counts.closed
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::first_crossing::Key;
    use crate::algorithms::first_crossing::packed::PackedKey;
    use crate::algorithms::first_crossing::word;

    thread_local! {
        pub(super) static PARALLEL_PHASES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    }

    // Use the production runner and serializer, but lower the parallel cutoff
    // on a small whole run. The phase counter belongs to this test's thread.
    #[test]
    fn parallel_whole_run_preserves_layers_channels_and_canonical_bytes() {
        let parameters = Parameters::new(4, None).unwrap();
        let mut expected = Vec::new();
        let counts = reference::for_each_layer(parameters, |sector, stage, rows| {
            expected.push((sector, stage, rows.to_vec()));
            Ok::<_, Infallible>(())
        })
        .unwrap();
        for threads in [2, 3] {
            PARALLEL_PHASES.set(0);
            let mut layers = expected.iter();
            let actual = run::<1, Infallible>(
                parameters,
                Config { threads },
                Some(&mut |sector, stage, rows| {
                    let (s, t, reference) = layers.next().unwrap();
                    assert_eq!((sector, stage, rows), (*s, *t, reference.as_slice()));
                    let bytes = |layer: &[ReferenceRow]| {
                        layer
                            .iter()
                            .map(crate::certify::first_crossing::row_text)
                            .collect::<String>()
                    };
                    assert_eq!(bytes(rows), bytes(reference));
                    Ok(())
                }),
            )
            .unwrap();
            assert!(layers.next().is_none());
            assert_eq!(actual, counts);
            assert!(PARALLEL_PHASES.get() > 0, "whole run must spawn workers");
            PARALLEL_PHASES.set(0);
            assert_eq!(
                run::<1, Infallible>(parameters, Config { threads }, None).unwrap(),
                counts
            );
            assert!(
                PARALLEL_PHASES.get() > 0,
                "count-only run must spawn workers"
            );
        }
    }

    #[test]
    fn complete_layers_match_reference_at_every_small_threshold() {
        for n in 0..=8 {
            let thresholds: Vec<_> = if n > 0 && n <= 6 {
                (1..=n).map(Some).collect()
            } else {
                vec![None]
            };
            for threshold in thresholds {
                let parameters = Parameters::new(n, threshold).unwrap();
                let mut expected = Vec::new();
                let counts = reference::for_each_layer(parameters, |s, t, rows| {
                    expected.push((s, t, rows.to_vec()));
                    Ok::<_, Infallible>(())
                })
                .unwrap();
                for threads in [1, 2, 3] {
                    let mut layers = expected.iter();
                    let actual =
                        for_each_layer_with_config(parameters, Config { threads }, |s, t, rows| {
                            let (es, et, erows) = layers.next().unwrap();
                            assert_eq!(
                                (s, t, rows),
                                (*es, *et, erows.as_slice()),
                                "n={n}, K={threshold:?}"
                            );
                            Ok::<_, Infallible>(())
                        })
                        .unwrap();
                    assert!(layers.next().is_none());
                    assert_eq!(actual, counts);
                    assert_eq!(
                        evaluate_with_threshold(n, threshold, Config { threads }).unwrap(),
                        counts
                    );
                }
            }
        }
    }

    fn tier<W: Weight>(
        sector: Sector,
        threads: usize,
        resume: Option<Widen<W>>,
    ) -> Result<Counts, Widen<W>> {
        scan_with::<W, Infallible>(
            sector,
            &mut Buffers::new(threads),
            &mut None,
            resume,
            PARALLEL_ROWS,
        )
        .unwrap()
    }

    /// Count one sector from a tier upward, widening whenever the mass bound
    /// requires it; returns the tiers used.
    fn count_from<W: Weight>(sector: Sector, threads: usize) -> (Counts, Vec<&'static str>) {
        let mut used = vec![std::any::type_name::<W>()];
        let widen = match tier::<W>(sector, threads, None) {
            Ok(counts) => return (counts, used),
            Err(widen) => widen.into::<u64>(),
        };
        used.push("u64");
        let widen = match tier(sector, threads, Some(widen)) {
            Ok(counts) => return (counts, used),
            Err(widen) => widen.into::<BigUint>(),
        };
        used.push("BigUint");
        (tier(sector, threads, Some(widen)).ok().unwrap(), used)
    }

    /// The mass bound widens narrow tiers before any checked sum can fail, so
    /// deliberately tiny tiers neither panic nor miscount, and the visitor
    /// sees every widened layer exactly once.
    #[test]
    fn weight_tiers_widen_exactly_and_agree_with_the_reference() {
        let mut widened = 0;
        for n in 1..=8 {
            let parameters = Parameters::new(n, None).unwrap();
            for sector in parameters.sectors() {
                let expected = reference::scan(sector, |_, _, _| Ok::<_, Infallible>(())).unwrap();
                for threads in [1, 3] {
                    for (counts, used) in [
                        count_from::<u8>(sector, threads),
                        count_from::<u16>(sector, threads),
                        count_from::<u64>(sector, threads),
                    ] {
                        assert_eq!(counts, expected, "{sector:?} via {used:?}");
                        widened += usize::from(used.len() > 1);
                    }
                }
            }
        }
        assert!(widened > 0);
        // A whole visited run from the tiny tier reports every layer once.
        let parameters = Parameters::new(7, None).unwrap();
        let mut expected = Vec::new();
        reference::for_each_layer(parameters, |s, t, rows| {
            expected.push((s, t, rows.to_vec()));
            Ok::<_, Infallible>(())
        })
        .unwrap();
        let mut seen = 0;
        for sector in parameters.sectors() {
            let mut visitor = |s: Sector, t: Stage, rows: &[ReferenceRow]| {
                let (es, et, erows) = &expected[seen];
                assert_eq!((s, t, rows), (*es, *et, erows.as_slice()));
                seen += 1;
                Ok::<_, Infallible>(())
            };
            let mut visitor: Option<&mut Visitor<'_, Infallible>> = Some(&mut visitor);
            let mut buffers = Buffers::new(2);
            let widen =
                match scan_with::<u8, _>(sector, &mut buffers, &mut visitor, None, 1).unwrap() {
                    Ok(_) => continue,
                    Err(widen) => widen.into::<BigUint>(),
                };
            let mut buffers = Buffers::new(2);
            scan_with(sector, &mut buffers, &mut visitor, Some(widen), 1)
                .unwrap()
                .ok()
                .unwrap();
        }
        assert_eq!(seen, expected.len());
    }

    /// A reference layer with several rows, at least one of which has a lower
    /// return label, so both weight channels are exercised.
    fn fixture() -> (Sector, Stage, Vec<ReferenceRow>) {
        let mut fixture = None;
        reference::for_each_layer(Parameters::new(6, None).unwrap(), |sector, stage, rows| {
            let returns = rows.iter().any(|row| {
                word::successors(sector, stage, word(sector, stage, &row.key))
                    .iter()
                    .any(|t| matches!(t, Some((_, true))))
            });
            if rows.len() >= 8 && returns {
                fixture = Some((sector, stage, rows.to_vec()));
                Err(())
            } else {
                Ok(())
            }
        })
        .unwrap_err();
        fixture.unwrap()
    }

    fn word(sector: Sector, stage: Stage, key: &Key) -> Word {
        let packed = PackedKey::encode(sector, stage, key).unwrap();
        Word::new(packed.counters(), packed.bits()).unwrap()
    }

    /// One layer transition on `threads` workers, flattened in bucket order,
    /// with the reduced row count and masses the workers published.
    fn next_layer<W: Weight>(
        sector: Sector,
        stage: Stage,
        rows: Vec<Row<W>>,
        threads: usize,
    ) -> (Vec<Row<W>>, usize, [u128; 2]) {
        let layer = empty_layer::<W>();
        for row in rows {
            layer[bucket(row.key)].lock().unwrap().push(row);
        }
        let pieces: Vec<_> = (0..threads).map(|_| empty_layer()).collect();
        let stop = AtomicBool::new(false);
        let shared = Shared::new(sector, &layer, &pieces, &stop, false, threads, 1);
        std::thread::scope(|scope| {
            for id in 0..threads {
                let shared = &shared;
                scope.spawn(move || step(shared, id, 0, stage, &mut Vec::new(), &mut Vec::new()));
            }
        });
        let rows: Vec<_> = layer
            .iter()
            .flat_map(|b| b.lock().unwrap().drain(..).collect::<Vec<_>>())
            .collect();
        let live = shared.live[0].load(Ordering::Acquire);
        let mass = *shared.mass[0].lock().unwrap();
        (rows, live, mass)
    }

    #[test]
    fn parallel_emission_preserves_collisions_and_large_weights() {
        let (sector, stage, rows) = fixture();
        let seeds: Vec<_> = rows
            .iter()
            .enumerate()
            .map(|(i, row)| Row::<BigUint> {
                key: word(sector, stage, &row.key),
                ordinary: row.weights.ordinary.clone() << 300,
                lower_returns: (row.weights.lower_returns.clone() << 300) + BigUint::from(i),
            })
            .collect();
        let input = || seeds.iter().cloned().cycle().take(8193).collect::<Vec<_>>();
        let (expected, live, mass) = next_layer(sector, stage, input(), 1);
        assert!(expected.len() > 1);
        assert_eq!(live, expected.len());
        assert_eq!(mass, [0; 2], "arbitrary precision is never measured");
        assert!(expected.iter().all(|row| row.ordinary.bits() > 128));
        let mut keys: Vec<_> = expected.iter().map(|row| row.key).collect();
        keys.dedup();
        assert_eq!(keys.len(), expected.len());
        let mut sum = BigUint::default();
        for row in &expected {
            sum += &row.ordinary;
        }
        let mut direct = BigUint::default();
        for row in &input() {
            let accepted = word::successors(sector, stage, row.key)
                .iter()
                .filter(|t| t.is_some())
                .count();
            direct += &row.ordinary * accepted;
        }
        assert_eq!(sum, direct);
        for threads in [2, 3, 64, 96, 128] {
            assert_eq!(
                next_layer(sector, stage, input(), threads).0,
                expected,
                "threads={threads}"
            );
        }
    }

    /// Requested worker counts above the old limit of 64 are used as
    /// requested up to one worker per bucket, produce the reference layers and
    /// counts, and allocate exactly one bucket set per effective worker.
    #[test]
    fn large_worker_requests_are_accepted_bounded_and_exact() {
        assert_eq!(Config { threads: 0 }.effective_threads(), 1);
        assert_eq!(Config { threads: 96 }.effective_threads(), 96);
        assert_eq!(Config { threads: 128 }.effective_threads(), 128);
        assert_eq!(
            Config {
                threads: MAX_WORKERS
            }
            .effective_threads(),
            MAX_WORKERS
        );
        assert_eq!(
            Config {
                threads: usize::MAX
            }
            .effective_threads(),
            MAX_WORKERS
        );
        let engine = Engine::new(
            Config {
                threads: usize::MAX,
            },
            PARALLEL_ROWS,
        );
        assert_eq!(engine.threads, MAX_WORKERS);
        assert_eq!(engine.narrow.pieces.len(), MAX_WORKERS);

        let parameters = Parameters::new(4, None).unwrap();
        let mut expected = Vec::new();
        let counts = reference::for_each_layer(parameters, |sector, stage, rows| {
            expected.push((sector, stage, rows.to_vec()));
            Ok::<_, Infallible>(())
        })
        .unwrap();
        for threads in [96, 128, MAX_WORKERS + 1] {
            PARALLEL_PHASES.set(0);
            let mut layers = expected.iter();
            let actual = run::<1, Infallible>(
                parameters,
                Config { threads },
                Some(&mut |sector, stage, rows| {
                    let (s, t, reference) = layers.next().unwrap();
                    assert_eq!((sector, stage, rows), (*s, *t, reference.as_slice()));
                    Ok(())
                }),
            )
            .unwrap();
            assert!(layers.next().is_none());
            assert_eq!(actual, counts, "threads={threads}");
            assert!(
                PARALLEL_PHASES.get() > 0,
                "threads={threads} must spawn workers"
            );
        }
        assert_eq!(
            evaluate_with_threshold(6, None, Config { threads: 128 }).unwrap(),
            evaluate_with_threshold(6, None, Config { threads: 1 }).unwrap()
        );
    }

    #[test]
    fn published_masses_are_exact_on_fixed_width_tiers() {
        let (sector, stage, rows) = fixture();
        let seeds: Vec<_> = rows
            .iter()
            .map(|row| Row {
                key: word(sector, stage, &row.key),
                ordinary: u64::MAX / 64,
                lower_returns: 3,
            })
            .collect();
        for threads in [1, 2] {
            let (layer, live, mass) = next_layer(sector, stage, seeds.clone(), threads);
            assert_eq!(live, layer.len());
            let expected = layer.iter().fold([0u128; 2], |[c, e], row| {
                [
                    c + u128::from(row.ordinary),
                    e + u128::from(row.lower_returns),
                ]
            });
            assert_eq!(mass, expected);
            assert!(expected[0] > u128::from(u64::MAX / 64));
        }
    }

    #[test]
    fn wide_sector_fallback_and_callback_stop_are_exact() {
        for parameters in [
            Parameters::new(66, Some(66)).unwrap(),
            Parameters::new(70_000, Some(1)).unwrap(),
        ] {
            let sector = parameters.sectors().next().unwrap();
            assert!(sector.port_bound() > CAPACITY || sector.budgets()[0] > usize::from(u16::MAX));
            let mut calls = 0;
            assert_eq!(
                Engine::new(Config::default(), PARALLEL_ROWS).scan(
                    sector,
                    Some(&mut |s: Sector, t: Stage, rows: &[ReferenceRow]| {
                        calls += 1;
                        assert_eq!(s, sector);
                        assert_eq!(t, s.initial_stage());
                        assert_eq!(rows.len(), 1);
                        assert_eq!(rows[0].key, Key::empty());
                        Err::<(), _>("stop")
                    })
                ),
                Err("stop")
            );
            assert_eq!(calls, 1);
        }
        assert_eq!(
            for_each_layer(
                Parameters::new(66, Some(66)).unwrap(),
                |_, _, _| Err::<(), _>("stop")
            ),
            Err("stop")
        );
        // A packed sector stops at the requested layer on every worker set.
        for threads in [1, 3] {
            let mut visited = Vec::new();
            let error = for_each_layer_with_config(
                Parameters::new(5, None).unwrap(),
                Config { threads },
                |sector, stage, _| {
                    visited.push((sector.is_high(), stage.tick));
                    if stage.tick == 3 { Err("stop") } else { Ok(()) }
                },
            )
            .unwrap_err();
            assert_eq!(error, "stop");
            assert_eq!(visited, [(false, 0), (false, 1), (false, 2), (false, 3)]);
        }
    }

    #[test]
    fn public_conventions_and_metadata_match_reference() {
        let evaluator = FirstCrossingOptimized {
            config: Config::default(),
        };
        for problem in Problem::ALL {
            assert_eq!(
                evaluator.max_order(*problem),
                reference::FirstCrossing.max_order(*problem)
            );
            for n in 0..=10 {
                assert_eq!(
                    evaluator.count(*problem, n),
                    reference::FirstCrossing.count(*problem, n)
                );
            }
        }
        assert_eq!(
            evaluator.count(Problem::Closed, usize::MAX),
            reference::FirstCrossing.count(Problem::Closed, usize::MAX)
        );
    }
}
