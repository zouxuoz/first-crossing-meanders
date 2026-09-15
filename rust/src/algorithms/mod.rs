//! Exact evaluators. Each one is a way of computing a meander number; the
//! Lean side (`Meanders/Algorithms/`) holds the proofs that the algorithm is
//! correct, and the certificate schema (`certify::Algorithm`) is the
//! registry that maps a tag to an implementation.

pub mod brute_force;
pub mod first_crossing;

use crate::problem::Problem;
use num_bigint::BigUint;
use std::{error::Error, fmt};

/// Invalid public input, rejected before evaluator execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvalError {
    OrderExceeded { n: usize, max: usize },
    FirstCrossing(first_crossing::InputError),
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FirstCrossing(error) => error.fmt(f),
            Self::OrderExceeded { n, max } => {
                write!(f, "order {n} exceeds evaluator maximum {max}")
            }
        }
    }
}

impl Error for EvalError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::FirstCrossing(error) => Some(error),
            Self::OrderExceeded { .. } => None,
        }
    }
}

/// Validate the public index before any metadata arithmetic.
pub(crate) fn check_order(n: usize, max: usize) -> Result<(), EvalError> {
    if n > max {
        Err(EvalError::OrderExceeded { n, max })
    } else {
        Ok(())
    }
}

/// Exact public results.
pub trait Evaluator: Sync {
    /// The largest public index accepted for a supported problem.
    fn max_order(&self, problem: Problem) -> usize;

    /// `Ok(None)` means unsupported; invalid supported inputs return an error.
    /// Invariant failures keep their checked panic behavior; this result is
    /// not a panic or allocation-failure wrapper.
    fn count(&self, problem: Problem, n: usize) -> Result<Option<BigUint>, EvalError>;
}

impl<T: Evaluator + ?Sized> Evaluator for &T {
    fn max_order(&self, problem: Problem) -> usize {
        (**self).max_order(problem)
    }

    fn count(&self, problem: Problem, n: usize) -> Result<Option<BigUint>, EvalError> {
        (**self).count(problem, n)
    }
}
