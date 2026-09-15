//! Direct surgery on packed Dyck words, with no decode, mate list or encode.
//!
//! A word position is a port in geometric cyclic order rev(PL),PR,rev(QR),QL;
//! bit 1 opens an arc. At a fixed stage the counters determine every guard,
//! the cup position, every reservoir top and every forced FIFO drain, so a
//! `Plan` compiles them once per counter block: each reference join becomes
//! the removal of two adjacent positions of the cup-extended word plus at
//! most one polarity flip of a partner. Only partner scans and the cycle
//! decision read the pairing bits. The differential tests compare every
//! labelled successor with `PackedKey::successors`, which decodes, calls
//! `advance` and encodes.

use super::packed::{CAPACITY, PackedKey};
use super::state::step_counters;
use super::{Move, Sector, Side, Stage};

/// Four u16 counters (lexicographic, PL first) in the high half and the
/// pairing word in the low half, so that sorted rows group by counter block.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct Word(u128);

impl Word {
    pub fn new(counters: [usize; 4], bits: u64) -> Option<Self> {
        let mut high = 0u64;
        for &c in &counters {
            high = (high << 16) | u64::from(u16::try_from(c).ok()?);
        }
        Some(Self((u128::from(high) << 64) | u128::from(bits)))
    }

    pub fn empty() -> Self {
        Self(0)
    }

    pub fn bits(self) -> u64 {
        self.0 as u64
    }

    /// The packed counters, identifying the counter block.
    pub fn block(self) -> u64 {
        (self.0 >> 64) as u64
    }

    pub fn counters(self) -> [usize; 4] {
        let high = self.block();
        std::array::from_fn(|g| ((high >> (48 - 16 * g)) & 0xFFFF) as usize)
    }

    pub fn packed(self) -> PackedKey {
        PackedKey::from_parts(self.counters(), self.bits())
    }

    /// Multiplicative mix of both halves; the top bits select a merge bucket.
    pub fn hash(self) -> u64 {
        let high = self.block().wrapping_mul(0x9E37_79B9_7F4A_7C15);
        let low = self.bits().wrapping_mul(0xC2B2_AE3D_27D4_EB4F);
        (high ^ low.rotate_left(29)).wrapping_mul(0x9E37_79B9_7F4A_7C15)
    }
}

/// Partner of the port at `at`, scanning outward from an opener or inward
/// from a closer.
fn partner(bits: u128, at: usize) -> usize {
    let open = bits & (1 << at) != 0;
    let mut depth = 1;
    let mut i = at;
    loop {
        if open {
            i += 1;
        } else {
            i -= 1;
        }
        if (bits & (1 << i) != 0) == open {
            depth += 1;
        } else {
            depth -= 1;
        }
        if depth == 0 {
            return i;
        }
    }
}

fn mask(len: usize) -> u128 {
    (1u128 << len) - 1
}

/// At most 66 port names on the stack: the retained capacity plus the cup.
#[derive(Clone, Copy)]
struct Ports {
    names: [u8; CAPACITY + 2],
    len: usize,
}

impl Ports {
    const EMPTY: Self = Self {
        names: [0; CAPACITY + 2],
        len: 0,
    };
    fn as_slice(&self) -> &[u8] {
        &self.names[..self.len]
    }
    fn push(&mut self, name: u8) {
        self.names[self.len] = name;
        self.len += 1;
    }
    fn pop(&mut self) -> u8 {
        self.len -= 1;
        self.names[self.len]
    }
    fn remove_first(&mut self) -> u8 {
        let first = self.names[0];
        self.names.copy_within(1..self.len, 0);
        self.len -= 1;
        first
    }
    fn position(&self, name: u8) -> usize {
        self.as_slice().iter().position(|&v| v == name).unwrap()
    }
    fn remove_pair(&mut self, x: u8, y: u8) {
        let mut kept = 0;
        for i in 0..self.len {
            let v = self.names[i];
            if v != x && v != y {
                self.names[kept] = v;
                kept += 1;
            }
        }
        self.len = kept;
    }
}

/// Geometric cyclic order rev(PL),PR,rev(QR),QL of four storage groups.
fn cyclic(groups: &[Ports; 4]) -> Ports {
    let mut order = Ports::EMPTY;
    for &name in groups[0].as_slice().iter().rev() {
        order.push(name);
    }
    for &name in groups[1].as_slice() {
        order.push(name);
    }
    for &name in groups[3].as_slice().iter().rev() {
        order.push(name);
    }
    for &name in groups[2].as_slice() {
        order.push(name);
    }
    order
}

/// One accepted label of a counter block. A step joins at most two cup
/// incidences and drains at most two pairs per side, so six joins suffice.
struct Target {
    word: u64,
    increment: bool,
    /// Positions of adjacent joins in the cup-extended word, in reference order.
    joins: [u8; 8],
    join_count: usize,
    live: usize,
    terminal: bool,
}

/// Every counter-dependent decision of one stage and counter block.
pub(super) struct Plan {
    block: u64,
    cup: usize,
    left: bool,
    targets: [Option<Target>; 4],
}

impl Plan {
    /// Compile the reference cup, P then Q attachment and P then Q drain
    /// sequence for reachable keys with these counters at this stage.
    pub(super) fn new(sector: Sector, stage: Stage, counters: [usize; 4]) -> Self {
        let geometry = sector.geometry(stage, counters);
        let mut offset = 0;
        let mut groups = [Ports::EMPTY; 4];
        for (group, &length) in groups.iter_mut().zip(&geometry.lengths) {
            for name in offset..offset + length {
                group.push(u8::try_from(name).expect("port capacity"));
            }
            offset += length;
        }
        assert!(offset <= CAPACITY);
        let side = sector.side_at(stage.tick);
        let left = side != Some(Side::Right);
        let s = usize::from(!left);
        let cup = geometry.lengths[0] + geometry.lengths[1];
        let mut cup_groups = groups;
        cup_groups[s].push(offset as u8);
        cup_groups[2 + s].push((offset + 1) as u8);
        let cup_order = cyclic(&cup_groups);
        let targets = std::array::from_fn(|label| {
            let label = Move::ALL[label];
            let (side, next_counters, increment) =
                step_counters(sector, stage, &geometry, counters, label)?;
            let next = stage.next(side);
            let downs = label.downs();
            let mut groups = groups;
            let mut pairs = [(0u8, 0u8); 8];
            let mut count = 0;
            let mut join = |x, y| {
                assert!(count < pairs.len(), "at most six joins per step");
                pairs[count] = (x, y);
                count += 1;
            };
            for (owner, down) in downs.into_iter().enumerate() {
                let g = 2 * owner + s;
                let cup = (offset + owner) as u8;
                if down {
                    join(groups[g].pop(), cup);
                } else {
                    groups[g].push(cup);
                }
            }
            if sector.is_high() {
                let after = sector.geometry(next, next_counters);
                for g in [0, 2] {
                    let before = geometry.emitted[g].min(geometry.emitted[g + 1]);
                    let drained = after.emitted[g].min(after.emitted[g + 1]);
                    for _ in before..drained {
                        join(groups[g].remove_first(), groups[g + 1].remove_first());
                    }
                }
            }
            let order = cyclic(&groups);
            assert!(order.len <= CAPACITY);
            let mut working = cup_order;
            let mut joins = [0u8; 8];
            for (i, &(x, y)) in pairs[..count].iter().enumerate() {
                let a = working.position(x);
                let b = working.position(y);
                assert_eq!(a.abs_diff(b), 1, "native cyclic seams are adjacent");
                working.remove_pair(x, y);
                joins[i] = a.min(b) as u8;
            }
            assert_eq!(
                working.as_slice(),
                order.as_slice(),
                "native destination cyclic order"
            );
            Some(Target {
                word: Word::new(next_counters, 0)
                    .expect("counters fit u16")
                    .block(),
                increment,
                joins,
                join_count: count,
                live: order.len,
                terminal: next.tick == sector.steps(),
            })
        });
        Self {
            block: Word::new(counters, 0).expect("counters fit u16").block(),
            cup,
            left,
            targets,
        }
    }

    pub(super) fn block(&self) -> u64 {
        self.block
    }

    /// All four labelled successors of a reachable word of this plan's block.
    pub(super) fn successors(&self, word: Word) -> [Option<(Word, bool)>; 4] {
        debug_assert_eq!(self.block, word.block());
        let bits = u128::from(word.bits());
        // The cup wraps the word on the left and sits at the PR/QR seam on the right.
        let initial = if self.left {
            (bits << 1) | 1
        } else {
            (bits & mask(self.cup)) | (1 << self.cup) | ((bits >> self.cup) << (self.cup + 2))
        };
        std::array::from_fn(|label| {
            let target = self.targets[label].as_ref()?;
            let mut bits = initial;
            let mut cycles = 0;
            for &at in &target.joins[..target.join_count] {
                let at = usize::from(at);
                // Equal letters hand the arc to a partner; () closes a
                // component and )( just deletes both ends.
                match (bits >> at) & 3 {
                    1 => {
                        cycles += 1;
                        if !target.terminal || target.live != 0 || cycles > 1 {
                            return None;
                        }
                    }
                    3 => bits |= 1 << partner(bits, at + 1),
                    0 => bits &= !(1 << partner(bits, at)),
                    _ => (),
                }
                bits = (bits & mask(at)) | ((bits >> (at + 2)) << at);
            }
            debug_assert_eq!(bits >> target.live, 0);
            let bits = u64::try_from(bits).expect("retained port capacity");
            Some((
                Word((u128::from(target.word) << 64) | u128::from(bits)),
                target.increment,
            ))
        })
    }
}

/// All four labelled successors of a reachable word at this stage.
#[cfg(test)]
pub(super) fn successors(sector: Sector, stage: Stage, word: Word) -> [Option<(Word, bool)>; 4] {
    Plan::new(sector, stage, word.counters()).successors(word)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::first_crossing::{Key, Parameters, advance, reference};
    use std::convert::Infallible;

    fn check_layer(sector: Sector, stage: Stage, rows: &[reference::Row]) {
        let mut scratch = Key::empty();
        for row in rows {
            let packed = PackedKey::encode(sector, stage, &row.key).unwrap();
            let word = Word::new(row.key.counters, packed.bits()).unwrap();
            assert_eq!(word.packed(), packed);
            let expected = packed.successors(sector, stage, &mut scratch).unwrap();
            let actual = successors(sector, stage, word);
            for (label, (a, e)) in Move::ALL.iter().zip(actual.into_iter().zip(expected)) {
                assert_eq!(
                    a.map(|(w, i)| (w.packed(), i)),
                    e,
                    "{sector:?} {stage:?} {:?} {label:?}",
                    row.key
                );
            }
        }
    }

    #[test]
    fn every_reachable_reference_successor_matches_word_surgery() {
        for n in 1..=8 {
            let thresholds: Vec<_> = if n <= 6 {
                (1..=n).collect()
            } else {
                vec![n / 2 + 1]
            };
            for threshold in thresholds {
                reference::for_each_layer(
                    Parameters::new(n, Some(threshold)).unwrap(),
                    |sector, stage, rows| {
                        check_layer(sector, stage, rows);
                        Ok::<_, Infallible>(())
                    },
                )
                .unwrap();
            }
        }
    }

    /// Wider words: the packed engine's own layers at order 11 and a narrow
    /// threshold, checked label by label against the codec-based successors.
    #[test]
    fn wide_word_successors_match_codec_successors() {
        for (n, threshold) in [(11, None), (10, Some(3)), (10, Some(9))] {
            crate::algorithms::first_crossing::optimized::for_each_layer(
                Parameters::new(n, threshold).unwrap(),
                |sector, stage, rows| {
                    check_layer(sector, stage, rows);
                    Ok::<_, Infallible>(())
                },
            )
            .unwrap();
        }
    }

    /// The temporary cup makes a 66-bit word at full capacity.
    #[test]
    fn full_capacity_cup_and_all_labels_match() {
        let sector = Parameters::new(33, Some(33))
            .unwrap()
            .sectors()
            .next()
            .unwrap();
        let mut stage = sector.initial_stage();
        let mut key = Key::empty();
        for _ in 0..32 {
            key = advance(sector, stage, &key, Move::UU).unwrap().0;
            stage = stage.next(Side::Left);
        }
        assert_eq!(key.mate.len(), CAPACITY);
        let packed = PackedKey::encode(sector, stage, &key).unwrap();
        let expected = packed.successors(sector, stage, &mut Key::empty()).unwrap();
        let actual = successors(
            sector,
            stage,
            Word::new(key.counters, packed.bits()).unwrap(),
        );
        assert_eq!(actual.map(|t| t.map(|(w, i)| (w.packed(), i))), expected);
    }

    #[test]
    fn word_halves_and_capacity_are_exact() {
        let word = Word::new([1, 2, 3, 65535], u64::MAX).unwrap();
        assert_eq!(word.counters(), [1, 2, 3, 65535]);
        assert_eq!(word.bits(), u64::MAX);
        assert_eq!(Word::new([0, 65536, 0, 0], 0), None);
        assert_eq!(Word::empty().counters(), [0; 4]);
        assert_ne!(Word::new([0; 4], 1).unwrap().hash(), Word::empty().hash());
        // Sorting groups counter blocks and orders them lexicographically.
        let a = Word::new([0, 0, 1, 0], u64::MAX).unwrap();
        let b = Word::new([0, 1, 0, 0], 0).unwrap();
        assert!(a < b);
        assert_eq!(a.block(), Word::new([0, 0, 1, 0], 7).unwrap().block());
    }
}
