//! Four owner/side groups, original counters, and incidence-path surgery.
//!
//! Storage is PL, PR, QL, QR, oldest first within each group. Noncrossing
//! cyclic order is rev(PL), PR, rev(QR), QL; it is not storage order.

use std::{error::Error, fmt};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InputError {
    MetadataOverflow { n: usize },
    InvalidThreshold { n: usize, threshold: usize },
}

impl fmt::Display for InputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MetadataOverflow { n } => {
                write!(f, "First-Crossing metadata exceeds usize at order {n}")
            }
            Self::InvalidThreshold { n, threshold } => {
                write!(f, "First-Crossing threshold {threshold} must be in 1..={n}")
            }
        }
    }
}

impl Error for InputError {}

/// Validated machine-sized metadata. Counts themselves are arbitrary precision.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Parameters {
    n: usize,
    threshold: usize,
    vertices: usize,
}

impl Parameters {
    pub fn new(n: usize, threshold: Option<usize>) -> Result<Self, InputError> {
        // Besides 2n physical vertices, surgery needs two temporary cup ports.
        let vertices = n
            .checked_mul(2)
            .filter(|v| v.checked_add(2).is_some())
            .ok_or(InputError::MetadataOverflow { n })?;
        // Rank zero has no sectors or first crossing; the threshold is unused.
        let threshold = if n == 0 {
            0
        } else {
            threshold.unwrap_or(n / 2 + 1)
        };
        if n > 0 && !(1..=n).contains(&threshold) {
            return Err(InputError::InvalidThreshold { n, threshold });
        }
        Ok(Self {
            n,
            threshold,
            vertices,
        })
    }

    pub fn order(self) -> usize {
        self.n
    }
    pub fn threshold(self) -> Option<usize> {
        (self.n > 0).then_some(self.threshold)
    }

    /// Native sector construction, LOW first, then lexicographic (L,u,v).
    /// Admissible zero-height candidates are retained; source-empty ones count zero.
    pub fn sectors(self) -> impl Iterator<Item = Sector> {
        let low = (self.n > 0).then_some(Sector {
            parameters: self,
            high: false,
            left: self.vertices,
            upper: 0,
            lower: 0,
            budgets: [self.n, 0, self.n, 0],
        });
        let high = (1..self.vertices).flat_map(move |left| {
            let right = self.vertices - left;
            let limit = left.min(right);
            (left % 2..=limit).step_by(2).filter_map(move |upper| {
                let lower = (2 * self.threshold).checked_sub(upper)?;
                (lower <= limit).then(|| Sector {
                    parameters: self,
                    high: true,
                    left,
                    upper,
                    lower,
                    budgets: [
                        (left - upper) / 2,
                        (right - upper) / 2,
                        (left - lower) / 2,
                        (right - lower) / 2,
                    ],
                })
            })
        });
        low.into_iter().chain(high)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Side {
    Left,
    Right,
}

impl Side {
    pub(super) fn index(self) -> usize {
        match self {
            Self::Left => 0,
            Self::Right => 1,
        }
    }
    fn other(self) -> Self {
        match self {
            Self::Left => Self::Right,
            Self::Right => Self::Left,
        }
    }
}

/// The four labels remain distinct when their successor keys coincide.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Move {
    UU,
    UD,
    DU,
    DD,
}

impl Move {
    pub const ALL: [Self; 4] = [Self::UU, Self::UD, Self::DU, Self::DD];
    pub(super) fn downs(self) -> [bool; 2] {
        match self {
            Self::UU => [false, false],
            Self::UD => [false, true],
            Self::DU => [true, false],
            Self::DD => [true, true],
        }
    }
}

/// Sector metadata belongs to the layer, never to its keys.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Sector {
    parameters: Parameters,
    high: bool,
    left: usize,
    upper: usize,
    lower: usize,
    budgets: [usize; 4],
}

impl Sector {
    pub fn order(self) -> usize {
        self.parameters.n
    }
    pub fn threshold(self) -> usize {
        self.parameters.threshold
    }
    pub fn is_high(self) -> bool {
        self.high
    }
    pub fn side_lengths(self) -> [usize; 2] {
        [self.left, self.parameters.vertices - self.left]
    }
    pub fn cut_heights(self) -> [usize; 2] {
        [self.upper, self.lower]
    }
    pub fn budgets(self) -> [usize; 4] {
        self.budgets
    }
    pub fn terminal_bonus(self) -> bool {
        self.high && self.lower > 0
    }
    pub fn steps(self) -> usize {
        self.parameters.vertices
    }

    /// Long side first and last; alternate long/short in the middle.
    pub fn side_at(self, tick: usize) -> Option<Side> {
        if tick >= self.steps() {
            return None;
        }
        if !self.high {
            return Some(Side::Left);
        }
        let delta = self.left.abs_diff(self.order());
        let long = if self.left < self.order() {
            Side::Right
        } else {
            Side::Left
        };
        Some(
            if tick < delta || tick >= self.steps() - delta || (tick - delta).is_multiple_of(2) {
                long
            } else {
                long.other()
            },
        )
    }

    pub fn initial_stage(self) -> Stage {
        Stage {
            tick: 0,
            processed: [0, 0],
        }
    }

    /// Reconstruct original heights and the FIFO/reservoir separator from
    /// original counters. Requires a key reachable at this sector's stage.
    pub fn geometry(self, stage: Stage, counters: [usize; 4]) -> Geometry {
        let heights = std::array::from_fn(|g| stage.processed[g % 2] - 2 * counters[g]);
        if !self.high {
            return Geometry {
                heights,
                emitted: [0; 4],
                reservoirs: heights,
                lengths: heights,
            };
        }
        let emitted =
            std::array::from_fn(|g| heights[g].saturating_sub(self.budgets[g] - counters[g]));
        let reservoirs = std::array::from_fn(|g| heights[g] - emitted[g]);
        let lengths =
            std::array::from_fn(|g| reservoirs[g] + emitted[g].saturating_sub(emitted[g ^ 1]));
        Geometry {
            heights,
            emitted,
            reservoirs,
            lengths,
        }
    }

    pub(super) fn port_bound(self) -> usize {
        if self.high {
            2 * (self.order() - self.threshold()) + 2
        } else {
            2 * (self.threshold() - 1)
        }
    }
}

/// Public trace metadata; constructed and advanced by the fixed sector schedule.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Stage {
    pub tick: usize,
    pub processed: [usize; 2],
}

impl Stage {
    pub(super) fn next(self, side: Side) -> Self {
        let mut next = self;
        next.tick += 1;
        next.processed[side.index()] += 1;
        next
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Geometry {
    pub heights: [usize; 4],
    pub emitted: [usize; 4],
    pub reservoirs: [usize; 4],
    pub lengths: [usize; 4],
}

/// Pairing names are consecutive positions in fixed group storage order.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Key {
    pub counters: [usize; 4],
    pub mate: Vec<usize>,
}

impl Key {
    pub fn empty() -> Self {
        Self {
            counters: [0; 4],
            mate: Vec::new(),
        }
    }
}

/// Endpoints stay named during surgery; None denotes a consumed incidence.
fn join(mate: &mut [Option<usize>], x: usize, y: usize) -> bool {
    assert_ne!(x, y);
    let a = mate[x].take().expect("live incidence");
    let b = mate[y].take().expect("live incidence");
    if a == y {
        assert_eq!(b, x);
        true
    } else {
        assert_ne!(b, x);
        mate[a] = Some(b);
        mate[b] = Some(a);
        false
    }
}

fn assert_noncrossing(groups: &[Vec<usize>; 4], mate: &[Option<usize>]) {
    let cyclic = groups[0]
        .iter()
        .rev()
        .chain(&groups[1])
        .chain(groups[3].iter().rev())
        .chain(&groups[2]);
    let mut seen = vec![false; mate.len()];
    let mut stack = Vec::new();
    for &x in cyclic {
        let y = mate[x].expect("group ports are live");
        assert_ne!(x, y);
        assert_eq!(mate[y], Some(x));
        if seen[x] {
            assert_eq!(stack.pop(), Some(x), "noncrossing cyclic order");
        } else {
            stack.push(y);
            seen[y] = true;
        }
    }
    assert!(stack.is_empty());
}

/// Counter update, rejection tests and the lower return increment of one
/// label, shared by the reference surgery and the packed word engine. The
/// geometry must be the caller's `sector.geometry(stage, counters)`.
pub(super) fn step_counters(
    sector: Sector,
    stage: Stage,
    geometry: &Geometry,
    counters: [usize; 4],
    label: Move,
) -> Option<(Side, [usize; 4], bool)> {
    let side = sector.side_at(stage.tick)?;
    let s = side.index();
    let downs = label.downs();
    // Read the ORIGINAL lower height before physical surgery or FIFO draining.
    let increment = downs[1] && geometry.heights[2 + s] == 1;
    let mut counters = counters;
    let remaining = sector.side_lengths()[s] - stage.processed[s] - 1;
    for (owner, down) in downs.into_iter().enumerate() {
        let g = 2 * owner + s;
        if down && geometry.reservoirs[g] == 0 {
            return None;
        }
        counters[g] += usize::from(down);
        let unused = sector.budgets[g].checked_sub(counters[g])?;
        if unused > remaining {
            return None;
        }
    }
    let next = stage.next(side);
    if side == Side::Left {
        let grade = next.processed[0] - counters[0] - counters[2];
        if sector.high {
            if (next.processed[0] < sector.left && grade >= sector.threshold())
                || (next.processed[0] == sector.left && grade != sector.threshold())
            {
                return None;
            }
        } else if grade >= sector.threshold() {
            return None;
        }
    }
    Some((side, counters, increment))
}

/// One labelled successor and its lower return increment. The caller supplies
/// a reachable key at the specified stage; this is not a malformed-key parser.
/// None rejects a label, including every outgoing label at terminal stage.
pub fn advance(sector: Sector, stage: Stage, key: &Key, label: Move) -> Option<(Key, bool)> {
    let geometry = sector.geometry(stage, key.counters);
    let (side, counters, increment) = step_counters(sector, stage, &geometry, key.counters, label)?;
    let s = side.index();
    let downs = label.downs();
    let next = stage.next(side);

    let mut offset = 0;
    let mut groups: [Vec<usize>; 4] = std::array::from_fn(|g| {
        let start = offset;
        offset += geometry.lengths[g];
        (start..offset).collect()
    });
    assert_eq!(offset, key.mate.len(), "counter-derived group lengths");
    let mut mate: Vec<_> = key.mate.iter().copied().map(Some).collect();
    mate.extend([Some(offset + 1), Some(offset)]);
    let mut cycles = 0;
    // Cup at the physical vertex, followed by its P then Q owner incidences.
    for (owner, down) in downs.into_iter().enumerate() {
        let g = 2 * owner + s;
        if down {
            let top = groups[g].pop().expect("available reservoir top");
            cycles += usize::from(join(&mut mate, top, offset + owner));
        } else {
            groups[g].push(offset + owner);
        }
    }
    assert_noncrossing(&groups, &mate);

    if sector.high {
        let new_geometry = sector.geometry(next, counters);
        // Forced ordinal pairs drain P before Q, each oldest-first.
        for g in [0, 2] {
            let before = geometry.emitted[g].min(geometry.emitted[g + 1]);
            let after = new_geometry.emitted[g].min(new_geometry.emitted[g + 1]);
            assert!(after >= before, "cumulative forced emissions are monotone");
            for _ in before..after {
                let x = groups[g].remove(0);
                let y = groups[g + 1].remove(0);
                cycles += usize::from(join(&mut mate, x, y));
                assert_noncrossing(&groups, &mate);
            }
        }
        assert_eq!(groups.each_ref().map(Vec::len), new_geometry.lengths);
    }
    let live = groups.iter().map(Vec::len).sum::<usize>();
    assert_eq!(live, mate.iter().filter(|m| m.is_some()).count());
    if cycles > 0 && !(cycles == 1 && next.tick == sector.steps() && live == 0) {
        return None;
    }
    assert!(live <= sector.port_bound());
    let flat: Vec<_> = groups.into_iter().flatten().collect();
    let mut rename = vec![usize::MAX; mate.len()];
    for (i, &x) in flat.iter().enumerate() {
        rename[x] = i;
    }
    let pairing = flat
        .into_iter()
        .map(|x| {
            let y = rename[mate[x].expect("surviving port")];
            assert_ne!(y, usize::MAX, "mate survives in a group");
            y
        })
        .collect();
    Some((
        Key {
            counters,
            mate: pairing,
        },
        increment,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn high(n: usize, left: usize, upper: usize, lower: usize) -> Sector {
        Parameters::new(n, None)
            .unwrap()
            .sectors()
            .find(|s| {
                s.is_high() && s.side_lengths()[0] == left && s.cut_heights() == [upper, lower]
            })
            .unwrap()
    }

    #[test]
    fn metadata_limits_are_checked() {
        assert!(Parameters::new(32, None).is_ok());
        assert!(Parameters::new((usize::MAX - 2) / 2, None).is_ok());
        for n in [usize::MAX / 2, usize::MAX] {
            assert_eq!(
                Parameters::new(n, None),
                Err(InputError::MetadataOverflow { n })
            );
        }
        for threshold in [0, 4] {
            assert_eq!(
                Parameters::new(3, Some(threshold)),
                Err(InputError::InvalidThreshold { n: 3, threshold })
            );
        }
        let zero = Parameters::new(0, Some(usize::MAX)).unwrap();
        assert_eq!(zero.threshold(), None);
        assert_eq!(zero.sectors().count(), 0);
    }

    #[test]
    fn asymmetric_schedules_visit_each_side_in_order() {
        use Side::{Left as L, Right as R};
        for (sector, expected) in [
            (high(3, 2, 2, 2), [R, R, L, R, L, R]),
            (high(3, 4, 2, 2), [L, L, R, L, R, L]),
            (high(3, 3, 1, 3), [L, R, L, R, L, R]),
        ] {
            assert_eq!(
                (0..6)
                    .map(|t| sector.side_at(t).unwrap())
                    .collect::<Vec<_>>(),
                expected
            );
            assert_eq!(sector.side_at(6), None);
        }
        for n in 1..=8 {
            for threshold in 1..=n {
                for sector in Parameters::new(n, Some(threshold)).unwrap().sectors() {
                    let mut stage = sector.initial_stage();
                    while let Some(side) = sector.side_at(stage.tick) {
                        stage = stage.next(side);
                    }
                    assert_eq!(stage.processed, sector.side_lengths());
                    assert_eq!(stage.tick, 2 * n);
                }
            }
        }
    }

    #[test]
    fn fifo_closure_is_accepted_only_at_the_sole_final_cycle() {
        let sector = high(1, 1, 1, 1);
        let initial = sector.initial_stage();
        let (one, increment) = advance(sector, initial, &Key::empty(), Move::UU).unwrap();
        assert!(!increment);
        let stage = initial.next(Side::Left);
        // No down moves: the physical cup survives until the P then Q FIFO joins.
        let (terminal, increment) = advance(sector, stage, &one, Move::UU).unwrap();
        assert!(!increment);
        assert_eq!(terminal.mate, Vec::<usize>::new());
        assert_eq!(terminal.counters, sector.budgets());
        for label in Move::ALL {
            assert_eq!(
                advance(sector, stage.next(Side::Right), &terminal, label),
                None
            );
        }
        let low = Parameters::new(2, None).unwrap().sectors().next().unwrap();
        let stage = low.initial_stage();
        let (one, _) = advance(low, stage, &Key::empty(), Move::UU).unwrap();
        assert_eq!(advance(low, stage.next(Side::Left), &one, Move::DD), None);
    }

    #[test]
    fn finishing_the_short_side_does_not_authorize_fifo_closure() {
        let sector = Parameters::new(2, Some(1))
            .unwrap()
            .sectors()
            .find(|s| s.is_high() && s.side_lengths()[0] == 1 && s.cut_heights() == [1, 1])
            .unwrap();
        // The short left side finishes now, but one right-side vertex remains.
        let stage = Stage {
            tick: 2,
            processed: [0, 2],
        };
        let key = Key {
            counters: [0; 4],
            mate: vec![2, 3, 0, 1],
        };
        assert_eq!(advance(sector, stage, &key, Move::UU), None);
    }

    #[test]
    fn simultaneous_fifo_cycles_are_rejected() {
        let sector = Parameters::new(6, Some(3))
            .unwrap()
            .sectors()
            .find(|s| s.is_high() && s.side_lengths()[0] == 4 && s.cut_heights() == [2, 4])
            .unwrap();
        let stage = Stage {
            tick: 8,
            processed: [3, 5],
        };
        let key = Key {
            counters: [1, 2, 0, 1],
            mate: vec![1, 0, 3, 2],
        };
        // The upper drain and the lower drain each close their own component.
        assert_eq!(advance(sector, stage, &key, Move::UU), None);
    }

    /// The pinned retained-height counterexample: an emitted mate was removed,
    /// so retained length one must not be mistaken for original height one.
    #[test]
    fn lower_event_reads_original_height_before_fifo_drain() {
        let sector = high(3, 2, 2, 2);
        let stage = Stage {
            tick: 5,
            processed: [2, 3],
        };
        let key = Key {
            counters: [0, 1, 0, 0],
            mate: vec![1, 0],
        };
        let geometry = sector.geometry(stage, key.counters);
        assert_eq!(geometry.heights[3], 3);
        assert_eq!(geometry.lengths[3], 1);
        let (terminal, increment) = advance(sector, stage, &key, Move::UD).unwrap();
        assert!(!increment);
        assert!(terminal.mate.is_empty());
        assert!(sector.terminal_bonus());
    }
}
