//! Shared inputs for evaluator tests. No evaluator is used to generate them.

use crate::problem::Problem;

/// `(order, count)` pairs from the shared known-value files.
pub(crate) fn golden(problem: Problem) -> Vec<(usize, u128)> {
    let text = match problem {
        Problem::Closed => include_str!("../../fixtures/oeis/closed.txt"),
        Problem::Open => include_str!("../../fixtures/oeis/open.txt"),
    };
    text.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            let mut fields = line.split_whitespace();
            let n = fields
                .next()
                .expect("order")
                .parse()
                .expect("numeric order");
            let count = fields
                .next()
                .expect("count")
                .parse()
                .expect("numeric count");
            assert!(fields.next().is_none(), "extra field in {problem}: {line}");
            (n, count)
        })
        .collect()
}
