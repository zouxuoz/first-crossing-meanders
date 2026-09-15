//! Exact oriented pairing compression, with no symmetry quotient.
//!
//! Bit i is an opening in geometric cyclic order rev(PL),PR,rev(QR),QL.
//! Group lengths are reconstructed from the layer and original counters. The
//! fixed-width representation has an explicit capacity; larger sectors retain
//! the exact reference representation rather than acquiring a new order limit.
//!
//! Production only decodes words produced by direct surgery in `word.rs`;
//! the encoder and the decode-advance-encode successors are the oracle the
//! differential tests compare that surgery against.

use super::{Geometry, Key, Sector, Stage};
#[cfg(test)]
use super::{Move, advance};

pub const CAPACITY: usize = u64::BITS as usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CodecError {
    InvalidGeometry,
    TooManyPorts,
    #[cfg(test)]
    InvalidPairing,
    InvalidBits,
}

/// All four original counters remain oriented and exact. No stored length,
/// marks, component names, or sector metadata are needed in the pairing key.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct PackedKey {
    counters: [usize; 4],
    bits: u64,
}

fn geometry(sector: Sector, stage: Stage, counters: [usize; 4]) -> Result<Geometry, CodecError> {
    let lengths = sector.side_lengths();
    if stage.tick > sector.steps()
        || stage.processed[0].checked_add(stage.processed[1]) != Some(stage.tick)
        || stage
            .processed
            .iter()
            .zip(lengths)
            .any(|(&n, limit)| n > limit)
        || counters.iter().enumerate().any(|(g, &n)| {
            n > sector.budgets()[g]
                || n.checked_mul(2)
                    .is_none_or(|twice| twice > stage.processed[g % 2])
        })
    {
        return Err(CodecError::InvalidGeometry);
    }
    Ok(sector.geometry(stage, counters))
}

/// Storage positions in geometric cyclic order, computed without heap storage.
fn cyclic_order(lengths: [usize; 4]) -> Result<([usize; CAPACITY], usize), CodecError> {
    let mut offsets = [0usize; 5];
    for g in 0..4 {
        offsets[g + 1] = offsets[g]
            .checked_add(lengths[g])
            .ok_or(CodecError::TooManyPorts)?;
    }
    let len = offsets[4];
    if len > CAPACITY {
        return Err(CodecError::TooManyPorts);
    }
    let mut order = [0; CAPACITY];
    let mut ordinal = 0;
    for (g, reverse) in [(0, true), (1, false), (3, true), (2, false)] {
        for i in 0..lengths[g] {
            order[ordinal] = offsets[g] + if reverse { lengths[g] - 1 - i } else { i };
            ordinal += 1;
        }
    }
    Ok((order, len))
}

impl PackedKey {
    #[cfg(test)]
    pub fn empty() -> Self {
        Self {
            counters: [0; 4],
            bits: 0,
        }
    }

    #[cfg(test)]
    pub fn counters(self) -> [usize; 4] {
        self.counters
    }

    #[cfg(test)]
    pub fn bits(self) -> u64 {
        self.bits
    }

    /// A word already produced by exact surgery; not a malformed-word parser.
    pub(super) fn from_parts(counters: [usize; 4], bits: u64) -> Self {
        Self { counters, bits }
    }

    /// Encode an involution only after checking its noncrossing cyclic order.
    #[cfg(test)]
    pub fn encode(sector: Sector, stage: Stage, key: &Key) -> Result<Self, CodecError> {
        let geometry = geometry(sector, stage, key.counters)?;
        let (order, len) = cyclic_order(geometry.lengths)?;
        if key.mate.len() != len {
            return Err(CodecError::InvalidPairing);
        }
        let mut ordinal = [0; CAPACITY];
        for i in 0..len {
            ordinal[order[i]] = i;
        }
        let mut expected = [0; CAPACITY];
        let mut depth = 0;
        let mut bits = 0;
        for (i, &x) in order[..len].iter().enumerate() {
            let y = key.mate[x];
            if y >= len || x == y || key.mate[y] != x {
                return Err(CodecError::InvalidPairing);
            }
            if ordinal[y] > i {
                bits |= 1u64 << i;
                expected[depth] = y;
                depth += 1;
            } else {
                if depth == 0 || expected[depth - 1] != x {
                    return Err(CodecError::InvalidPairing);
                }
                depth -= 1;
            }
        }
        if depth != 0 {
            return Err(CodecError::InvalidPairing);
        }
        Ok(Self {
            counters: key.counters,
            bits,
        })
    }

    /// Decode into reusable scratch storage. All malformed bit words reject.
    pub fn decode_into(
        self,
        sector: Sector,
        stage: Stage,
        key: &mut Key,
    ) -> Result<(), CodecError> {
        let geometry = geometry(sector, stage, self.counters)?;
        let (order, len) = cyclic_order(geometry.lengths)?;
        if len < CAPACITY && self.bits >> len != 0 {
            return Err(CodecError::InvalidBits);
        }
        key.counters = self.counters;
        key.mate.clear();
        key.mate.resize(len, 0);
        let mut stack = [0; CAPACITY];
        let mut depth = 0;
        for (i, &x) in order[..len].iter().enumerate() {
            if self.bits & (1u64 << i) != 0 {
                stack[depth] = x;
                depth += 1;
            } else {
                if depth == 0 {
                    return Err(CodecError::InvalidBits);
                }
                depth -= 1;
                let y = stack[depth];
                key.mate[x] = y;
                key.mate[y] = x;
            }
        }
        if depth != 0 {
            return Err(CodecError::InvalidBits);
        }
        Ok(())
    }

    pub fn decode(self, sector: Sector, stage: Stage) -> Result<Key, CodecError> {
        let mut key = Key::empty();
        self.decode_into(sector, stage, &mut key)?;
        Ok(key)
    }

    /// Decode once and reuse the single reference transition for all four labels.
    /// As with `advance`, the key/stage must belong to this sector's reachable layer.
    #[cfg(test)]
    pub fn successors(
        self,
        sector: Sector,
        stage: Stage,
        scratch: &mut Key,
    ) -> Result<[Option<(Self, bool)>; 4], CodecError> {
        self.decode_into(sector, stage, scratch)?;
        let Some(side) = sector.side_at(stage.tick) else {
            return Ok([None; 4]);
        };
        let next = stage.next(side);
        let mut targets = [None; 4];
        for (slot, label) in targets.iter_mut().zip(Move::ALL) {
            if let Some((key, increment)) = advance(sector, stage, scratch, label) {
                *slot = Some((Self::encode(sector, next, &key)?, increment));
            }
        }
        Ok(targets)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::first_crossing::{Parameters, reference};
    use std::convert::Infallible;

    #[test]
    fn every_reachable_key_and_label_roundtrips() {
        for n in 1..=8 {
            let thresholds: Vec<_> = if n <= 6 {
                (1..=n).collect()
            } else {
                vec![n / 2 + 1]
            };
            for threshold in thresholds {
                reference::for_each_layer(Parameters::new(n, Some(threshold)).unwrap(), |sector, stage, rows| {
                    let mut scratch = Key::empty();
                    for row in rows {
                        let packed = PackedKey::encode(sector, stage, &row.key).unwrap();
                        assert_eq!(packed.decode(sector, stage).unwrap(), row.key);
                        if let Some(side) = sector.side_at(stage.tick) {
                            let actual = packed.successors(sector, stage, &mut scratch).unwrap();
                            for (slot, label) in actual.into_iter().zip(Move::ALL) {
                                let expected = advance(sector, stage, &row.key, label);
                                assert_eq!(slot.map(|(key, e)| (key.decode(sector, stage.next(side)).unwrap(), e)), expected,
                                    "n={n}, K={threshold}, sector={sector:?}, stage={stage:?}, label={label:?}");
                            }
                        }
                    }
                    Ok::<_, Infallible>(())
                }).unwrap();
            }
        }
    }

    #[test]
    fn capacity_and_malformed_words_are_checked() {
        let sector = Parameters::new(64, Some(64))
            .unwrap()
            .sectors()
            .next()
            .unwrap();
        let stage = Stage {
            tick: 32,
            processed: [32, 0],
        };
        let geometry = sector.geometry(stage, [0; 4]);
        let (order, len) = cyclic_order(geometry.lengths).unwrap();
        assert_eq!(len, CAPACITY);
        let mut key = Key {
            counters: [0; 4],
            mate: vec![0; len],
        };
        for pair in order[..len].as_chunks::<2>().0 {
            key.mate[pair[0]] = pair[1];
            key.mate[pair[1]] = pair[0];
        }
        let packed = PackedKey::encode(sector, stage, &key).unwrap();
        assert_eq!(packed.decode(sector, stage).unwrap(), key);
        for bits in [0, u64::MAX, 2] {
            assert_eq!(
                PackedKey {
                    counters: [0; 4],
                    bits
                }
                .decode(sector, stage),
                Err(CodecError::InvalidBits)
            );
        }
        let too_wide = Stage {
            tick: 33,
            processed: [33, 0],
        };
        assert_eq!(
            packed.decode(sector, too_wide),
            Err(CodecError::TooManyPorts)
        );
        key.mate[0] = 0;
        assert_eq!(
            PackedKey::encode(sector, stage, &key),
            Err(CodecError::InvalidPairing)
        );
        assert_eq!(
            PackedKey {
                counters: [0; 4],
                bits: 1
            }
            .decode(sector, sector.initial_stage()),
            Err(CodecError::InvalidBits)
        );
        assert_eq!(
            PackedKey::empty().decode(
                sector,
                Stage {
                    tick: 1,
                    processed: [0, 0]
                }
            ),
            Err(CodecError::InvalidGeometry)
        );
    }
}
