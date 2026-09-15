//! Shared First-Crossing carrier for Closed and Open meanders.
//!
//! The reference follows the First-Crossing construction in the blueprint and
//! the executable Lean model.
//! The `first_crossing` evaluator emits sector lower-jet certificates through
//! the shared registry; count-only claims remain readable.

pub mod optimized;
pub mod packed;
pub mod reference;
mod state;
mod word;

pub use state::{Geometry, InputError, Key, Move, Parameters, Sector, Side, Stage, advance};
