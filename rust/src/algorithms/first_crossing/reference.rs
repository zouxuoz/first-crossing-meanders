//! Deterministic sequential sectors and sorted two-buffer paired propagation.

use super::{InputError, Key, Move, Parameters, Sector, Stage, advance};
use crate::algorithms::{EvalError, Evaluator, check_order};
use crate::problem::Problem;
use num_bigint::BigUint;

/// Both channels merge additively even when the lower moment is zero.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Weights {
    pub ordinary: BigUint,
    pub lower_returns: BigUint,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Row {
    pub key: Key,
    pub weights: Weights,
}

/// Closed(n) and Open(2n) from one shared run. At positive n, `closed` is
/// also Open(2n-1). At n=0 these are exactly (0,1), with no previous odd alias.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Counts {
    pub closed: BigUint,
    pub open_even: BigUint,
}

/// Sort by the complete key and combine both moments in place. Equal labelled
/// successors are contributions, never a set of distinct destination keys.
fn merge(rows: &mut Vec<Row>) {
    rows.sort_unstable_by(|a, b| a.key.cmp(&b.key));
    rows.dedup_by(|later, earlier| {
        if later.key == earlier.key {
            earlier.weights.ordinary += std::mem::take(&mut later.weights.ordinary);
            earlier.weights.lower_returns += std::mem::take(&mut later.weights.lower_returns);
            true
        } else {
            false
        }
    });
}

/// Scan one validated sector. The callback sees the seed and every complete
/// sorted layer, including empty layers. Its error immediately stops execution.
/// The terminal layer contains unbonused lower returns; the result applies the
/// sector's through-arch bonus exactly once, after terminal validation.
pub fn scan<E>(
    sector: Sector,
    mut visit: impl FnMut(Sector, Stage, &[Row]) -> Result<(), E>,
) -> Result<Counts, E> {
    let mut current = vec![Row {
        key: Key::empty(),
        weights: Weights {
            ordinary: 1u32.into(),
            lower_returns: BigUint::default(),
        },
    }];
    let mut next = Vec::new();
    let mut stage = sector.initial_stage();
    visit(sector, stage, &current)?;
    while let Some(side) = sector.side_at(stage.tick) {
        for row in &current {
            for label in Move::ALL {
                if let Some((key, increment)) = advance(sector, stage, &row.key, label) {
                    let mut weights = row.weights.clone();
                    if increment {
                        weights.lower_returns += &row.weights.ordinary;
                    }
                    next.push(Row { key, weights });
                }
            }
        }
        merge(&mut next);
        current.clear();
        std::mem::swap(&mut current, &mut next);
        stage = stage.next(side);
        visit(sector, stage, &current)?;
    }
    let mut counts = Counts::default();
    for row in current {
        assert_eq!(row.key.counters, sector.budgets(), "terminal down budgets");
        assert!(row.key.mate.is_empty(), "terminal frontier is empty");
        counts.closed += row.weights.ordinary;
        counts.open_even += row.weights.lower_returns;
    }
    if sector.terminal_bonus() {
        counts.open_even += &counts.closed;
    }
    Ok(counts)
}

/// Run sequential sectors without retaining their traces or terminal layers.
/// Validate inputs with `Parameters::new` before supplying an effectful callback.
pub fn for_each_layer<E>(
    parameters: Parameters,
    mut visit: impl FnMut(Sector, Stage, &[Row]) -> Result<(), E>,
) -> Result<Counts, E> {
    if parameters.order() == 0 {
        return Ok(Counts {
            closed: BigUint::default(),
            open_even: 1u32.into(),
        });
    }
    let mut counts = Counts::default();
    for sector in parameters.sectors() {
        let part = scan(sector, &mut visit)?;
        counts.closed += part.closed;
        counts.open_even += part.open_even;
    }
    Ok(counts)
}

#[cfg(test)]
pub fn evaluate_with_threshold(n: usize, threshold: Option<usize>) -> Result<Counts, InputError> {
    let parameters = Parameters::new(n, threshold)?;
    Ok(for_each_layer(parameters, |_, _, _| Ok::<_, std::convert::Infallible>(())).unwrap())
}

pub fn evaluate(n: usize) -> Result<Counts, InputError> {
    let parameters = Parameters::new(n, None)?;
    Ok(for_each_layer(parameters, |_, _, _| Ok::<_, std::convert::Infallible>(())).unwrap())
}

/// Public Closed/Open conventions. The Open dispatch
/// uses ceil(m/2) without computing m+1, which could overflow machine metadata.
pub fn count(problem: Problem, n: usize) -> Result<Option<BigUint>, InputError> {
    match problem {
        Problem::Closed => Ok(Some(evaluate(n)?.closed)),
        Problem::Open => {
            let counts = evaluate(n.div_ceil(2))?;
            Ok(Some(if n % 2 == 1 {
                counts.closed
            } else {
                counts.open_even
            }))
        }
    }
}

/// Readable shared-carrier evaluator exposed through the public registry.
pub struct FirstCrossing;

impl Evaluator for FirstCrossing {
    fn max_order(&self, problem: Problem) -> usize {
        // Parameters require 2 * rank + 2 to fit machine-sized metadata.
        let rank = (usize::MAX - 2) / 2;
        match problem {
            Problem::Closed => rank,
            Problem::Open => 2 * rank,
        }
    }

    fn count(&self, problem: Problem, n: usize) -> Result<Option<BigUint>, EvalError> {
        check_order(n, self.max_order(problem))?;
        count(problem, n).map_err(EvalError::FirstCrossing)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::brute_force;
    use crate::test_support::golden;
    use std::convert::Infallible;

    #[test]
    fn metadata_limits_follow_the_public_problem_index() {
        let closed_max = FirstCrossing.max_order(Problem::Closed);
        let open_max = FirstCrossing.max_order(Problem::Open);
        assert_eq!(closed_max, (usize::MAX - 2) / 2);
        assert_eq!(open_max, 2 * closed_max);
        assert!(Parameters::new(closed_max, None).is_ok());
        assert!(Parameters::new(closed_max + 1, None).is_err());
        for n in [open_max - 1, open_max] {
            assert!(Parameters::new(n.div_ceil(2), None).is_ok());
        }
        assert!(Parameters::new((open_max + 1).div_ceil(2), None).is_err());
    }

    #[test]
    fn public_counts_match_independent_enumeration_and_golden_values() {
        assert_eq!(count(Problem::Closed, 0).unwrap(), Some(0u32.into()));
        assert_eq!(count(Problem::Open, 0).unwrap(), Some(1u32.into()));
        // Pinned OEIS A005316 data, shared with the Lean known-value table,
        // keeps the open-even n=7,8 checks independent of this evaluator.
        let open_golden = golden(Problem::Open);
        for n in 1..=8 {
            let actual = evaluate(n).unwrap();
            assert_eq!(
                actual.closed,
                BigUint::from(brute_force::count_closed_meanders(n)),
                "Closed({n})"
            );
            let expected_open = open_golden.iter().find(|(q, _)| *q == 2 * n).unwrap().1;
            assert_eq!(
                actual.open_even,
                BigUint::from(expected_open),
                "Open({})",
                2 * n
            );
            assert_eq!(
                count(Problem::Open, 2 * n - 1).unwrap(),
                Some(actual.closed.clone())
            );
            assert_eq!(
                count(Problem::Open, 2 * n).unwrap(),
                Some(actual.open_even.clone())
            );
            if n <= 6 {
                assert_eq!(
                    actual.open_even,
                    BigUint::from(brute_force::count_open_meanders(2 * n))
                );
                for threshold in 1..=n {
                    assert_eq!(
                        evaluate_with_threshold(n, Some(threshold)).unwrap(),
                        actual,
                        "n={n}, K={threshold}"
                    );
                }
            }
        }
    }

    #[test]
    fn callback_stops_before_any_further_layer_or_sector() {
        let mut visited = Vec::new();
        let error = for_each_layer(Parameters::new(3, None).unwrap(), |sector, stage, _| {
            visited.push((sector.is_high(), stage.tick));
            if stage.tick == 2 { Err("stop") } else { Ok(()) }
        })
        .unwrap_err();
        assert_eq!(error, "stop");
        assert_eq!(visited, [(false, 0), (false, 1), (false, 2)]);
        let zero = for_each_layer(
            Parameters::new(0, None).unwrap(),
            |_, _, _| -> Result<(), Infallible> {
                panic!("zero has no sectors");
            },
        )
        .unwrap();
        assert_eq!(
            zero,
            Counts {
                closed: 0u32.into(),
                open_even: 1u32.into()
            }
        );
    }

    #[test]
    fn terminal_bonus_does_not_mutate_the_lower_return_trace() {
        let sector = Parameters::new(1, None)
            .unwrap()
            .sectors()
            .find(|s| s.is_high())
            .unwrap();
        let mut terminal = None;
        let counts = scan(sector, |_, stage, rows| {
            if stage.tick == 2 {
                terminal = Some(rows.to_vec());
            }
            Ok::<_, Infallible>(())
        })
        .unwrap();
        assert_eq!(
            terminal.unwrap()[0].weights,
            Weights {
                ordinary: 1u32.into(),
                lower_returns: 0u32.into()
            }
        );
        assert_eq!(
            counts,
            Counts {
                closed: 1u32.into(),
                open_even: 1u32.into()
            }
        );
    }

    /// Equal keys forget past exterior counts; their first moments must add.
    #[test]
    fn history_collision_keeps_both_weights() {
        let sector = Parameters::new(2, None).unwrap().sectors().next().unwrap();
        let mut witness = None;
        scan(sector, |_, stage, rows| {
            if stage.tick == 3 {
                witness = rows
                    .iter()
                    .find(|row| {
                        row.key
                            == Key {
                                counters: [1, 0, 1, 0],
                                mate: vec![1, 0],
                            }
                    })
                    .cloned();
            }
            Ok::<_, Infallible>(())
        })
        .unwrap();
        assert_eq!(
            witness.unwrap().weights,
            Weights {
                ordinary: 2u32.into(),
                lower_returns: 1u32.into()
            }
        );
    }

    #[test]
    fn colliding_rows_merge_exactly_above_machine_count_width() {
        let huge = BigUint::from(1u32) << 256usize;
        let mut rows = vec![
            Row {
                key: Key::empty(),
                weights: Weights {
                    ordinary: huge.clone(),
                    lower_returns: 0u32.into(),
                },
            },
            Row {
                key: Key::empty(),
                weights: Weights {
                    ordinary: huge.clone(),
                    lower_returns: huge.clone(),
                },
            },
            Row {
                key: Key::empty(),
                weights: Weights {
                    ordinary: 1u32.into(),
                    lower_returns: 3u32.into(),
                },
            },
        ];
        merge(&mut rows);
        assert_eq!(rows.len(), 1);
        assert_eq!(
            rows[0].weights,
            Weights {
                ordinary: &huge * 2u32 + 1u32,
                lower_returns: huge + 3u32
            }
        );
    }
}
