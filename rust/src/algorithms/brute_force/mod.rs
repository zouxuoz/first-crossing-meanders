//! Brute-force meander counting.
//!
//! Deliberately the most obvious algorithm there is: enumerate every
//! noncrossing perfect matching of the `2n` boundary points, take every
//! ordered pair of them (closed meanders), and keep the overlays that are a single
//! closed curve. It is `catalan(n)^2` walks for closed meanders, so it dies
//! somewhere around `n = 12`; speed is not the point. The point is that it is
//! simple enough to read against `Meanders/Algorithms/BruteForce.lean`, whose
//! correctness theorems are what give the counts their meaning.
//!
//! Matchings are represented by their partner array: `partner[i]` is the point
//! matched to `i`. Noncrossing perfect matchings of `2n` points correspond to
//! balanced bracket words of length `2n`, so they are enumerated as words and
//! decoded with a stack.

use super::{EvalError, Evaluator, check_order};
use crate::problem::Problem;
use num_bigint::BigUint;

/// The largest order this module will handle; partner arrays are `u8`.
/// Far beyond anything brute force can finish anyway.
pub const MAX_ORDER: usize = 127;

/// The brute-force evaluator, registered as `certify::Algorithm::BruteForce`.
pub struct BruteForce;

impl Evaluator for BruteForce {
    fn max_order(&self, _problem: Problem) -> usize {
        MAX_ORDER
    }

    fn count(&self, problem: Problem, n: usize) -> Result<Option<BigUint>, EvalError> {
        check_order(n, MAX_ORDER)?;
        let count = match problem {
            Problem::Closed => Some(count_closed_meanders(n)),
            Problem::Open => Some(count_open_meanders(n)),
        };
        Ok(count.map(BigUint::from))
    }
}

/// Every balanced bracket word of length `2n`, `true` for an opening bracket.
fn balanced_words(n: usize) -> Vec<Vec<bool>> {
    fn rec(n: usize, open: usize, close: usize, cur: &mut Vec<bool>, out: &mut Vec<Vec<bool>>) {
        if cur.len() == 2 * n {
            out.push(cur.clone());
            return;
        }
        if open < n {
            cur.push(true);
            rec(n, open + 1, close, cur, out);
            cur.pop();
        }
        if close < open {
            cur.push(false);
            rec(n, open, close + 1, cur, out);
            cur.pop();
        }
    }

    let mut out = Vec::new();
    rec(n, 0, 0, &mut Vec::with_capacity(2 * n), &mut out);
    out
}

/// Decode a balanced word into a partner array: each closing bracket is
/// matched to the most recent unmatched opening bracket.
fn partner_array(word: &[bool]) -> Vec<u8> {
    let mut stack: Vec<usize> = Vec::with_capacity(word.len() / 2);
    let mut partner = vec![0u8; word.len()];
    for (i, &open) in word.iter().enumerate() {
        if open {
            stack.push(i);
        } else {
            let j = stack.pop().expect("word is balanced");
            partner[i] = j as u8;
            partner[j] = i as u8;
        }
    }
    partner
}

/// Every noncrossing perfect matching of `2n` points, as partner arrays.
/// There are `catalan(n)` of them.
pub fn matchings(n: usize) -> Vec<Vec<u8>> {
    assert!(n <= MAX_ORDER, "order {n} exceeds MAX_ORDER {MAX_ORDER}");
    balanced_words(n).iter().map(|w| partner_array(w)).collect()
}

/// Is the superposition of `above` and `below` a single closed curve?
///
/// Every point has degree two in the superposition (one arch from each
/// matching), so the union is a disjoint set of closed curves. Walking from
/// point `0` and alternating the two matchings therefore traverses exactly the
/// curve through `0`, returning to `0` after as many steps as that curve is
/// long. It is the whole diagram precisely when that length is `2n`.
pub fn is_single_loop(above: &[u8], below: &[u8]) -> bool {
    let len = above.len();
    if len == 0 {
        return false;
    }
    let mut v = 0usize;
    let mut steps = 0usize;
    loop {
        v = above[v] as usize;
        v = below[v] as usize;
        steps += 2;
        if v == 0 {
            return steps == len;
        }
        if steps > len {
            // Unreachable for genuine matchings; a guard, not a code path.
            return false;
        }
    }
}

/// The number of closed meanders of order `n`. Order `0` has no crossings and
/// hence no curve, so it counts `0`.
pub fn count_closed_meanders(n: usize) -> u128 {
    if n == 0 {
        return 0;
    }
    let ms = matchings(n);
    let mut total = 0u128;
    for above in &ms {
        for below in &ms {
            if is_single_loop(above, below) {
                total += 1;
            }
        }
    }
    total
}

/// Connectedness after deleting one lower arch, retaining every upper edge.
fn cut_connected(above: &[u8], below: &[u8], left: usize) -> bool {
    let right = below[left] as usize;
    let mut seen = vec![false; above.len()];
    let mut pending = vec![left];
    seen[left] = true;
    while let Some(v) = pending.pop() {
        let mut visit = |u: usize| {
            if !seen[u] {
                seen[u] = true;
                pending.push(u);
            }
        };
        visit(above[v] as usize);
        if v != left && v != right {
            visit(below[v] as usize);
        }
    }
    seen.into_iter().all(|v| v)
}

/// Enumerate the geometric open diagrams, independently of active boundary transitions.
pub fn count_open_meanders(q: usize) -> u128 {
    assert!(q <= MAX_ORDER, "crossings {q} exceed MAX_ORDER {MAX_ORDER}");
    if q == 0 {
        return 1;
    }
    if q % 2 == 1 {
        return count_closed_meanders(q / 2 + 1);
    }
    let ms = matchings(q / 2);
    let mut total = 0u128;
    for upper in &ms {
        for lower in &ms {
            for left in 0..q {
                let right = lower[left] as usize;
                let exterior = left < right && !(0..left).any(|i| right < lower[i] as usize);
                if exterior && cut_connected(upper, lower, left) {
                    total = total.checked_add(1).expect("open count overflows u128");
                }
            }
        }
    }
    total
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::golden;
    use proptest::prelude::*;
    use std::collections::BTreeSet;

    /// Reference implementation of the connected component of point `0`,
    /// by breadth-first search rather than by walking the curve.
    fn component_of_zero(above: &[u8], below: &[u8]) -> BTreeSet<usize> {
        let mut seen = BTreeSet::new();
        let mut queue = vec![0usize];
        seen.insert(0usize);
        while let Some(v) = queue.pop() {
            for &next in &[above[v] as usize, below[v] as usize] {
                if seen.insert(next) {
                    queue.push(next);
                }
            }
        }
        seen
    }

    /// The points the alternating walk of `is_single_loop` actually visits.
    fn loop_walk(above: &[u8], below: &[u8]) -> BTreeSet<usize> {
        let mut seen = BTreeSet::new();
        let mut v = 0usize;
        seen.insert(0usize);
        for _ in 0..above.len() {
            v = above[v] as usize;
            seen.insert(v);
            v = below[v] as usize;
            seen.insert(v);
            if v == 0 {
                break;
            }
        }
        seen
    }

    #[test]
    fn matchings_are_catalan_many() {
        // catalan(0..=8)
        let catalan = [1usize, 1, 2, 5, 14, 42, 132, 429, 1430];
        for (n, &expected) in catalan.iter().enumerate() {
            assert_eq!(matchings(n).len(), expected, "order {n}");
        }
    }

    #[test]
    fn matchings_are_involutions_without_fixed_points() {
        for n in 0..=6 {
            for m in matchings(n) {
                for i in 0..m.len() {
                    let j = m[i] as usize;
                    assert_ne!(j, i, "order {n}: point {i} matched to itself");
                    assert_eq!(m[j] as usize, i, "order {n}: partner is not an involution");
                }
            }
        }
    }

    #[test]
    fn matchings_are_noncrossing() {
        for n in 0..=6 {
            for m in matchings(n) {
                for i in 0..m.len() {
                    for k in 0..m.len() {
                        let (j, l) = (m[i] as usize, m[k] as usize);
                        // i < k < j < l is the forbidden interleaving.
                        assert!(
                            !(i < k && k < j && j < l),
                            "order {n}: {i}-{j} crosses {k}-{l}"
                        );
                    }
                }
            }
        }
    }

    /// The counts must reproduce the shared golden file. Orders past 7 take
    /// minutes in a debug build, so they are exercised by `--release` runs and
    /// by the certificate pipeline instead.
    #[test]
    fn counts_match_golden_file() {
        let golden = golden(Problem::Closed);
        assert!(golden.len() >= 8, "golden file looks truncated");
        for (n, expected) in golden.into_iter().filter(|&(n, _)| n <= 7) {
            assert_eq!(count_closed_meanders(n), expected, "order {n}");
        }
    }

    proptest! {
        /// The alternating walk sees exactly the component of point 0 — the
        /// fact that lets `is_single_loop` decide connectivity in one pass.
        #[test]
        fn walk_visits_exactly_the_component(n in 1usize..=6, i: usize, j: usize) {
            let ms = matchings(n);
            let above = &ms[i % ms.len()];
            let below = &ms[j % ms.len()];
            prop_assert_eq!(loop_walk(above, below), component_of_zero(above, below));
        }

        /// ... so it agrees with a component-size test.
        #[test]
        fn single_loop_iff_component_is_everything(n in 1usize..=6, i: usize, j: usize) {
            let ms = matchings(n);
            let above = &ms[i % ms.len()];
            let below = &ms[j % ms.len()];
            prop_assert_eq!(
                is_single_loop(above, below),
                component_of_zero(above, below).len() == 2 * n
            );
        }
    }
}
