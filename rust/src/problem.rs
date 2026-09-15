//! The counting problems, mirrored from `Meanders.Problem` in
//! `Meanders/Problems/Problem.lean`. Serialized as the `problem` field of a
//! certificate, so the tag can never be misspelled here.

use std::fmt;
use std::str::FromStr;

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Problem {
    /// Closed meanders: a closed curve crossing a line `2n` times (OEIS A005315).
    Closed,
    /// Open meanders, indexed by genuine crossings; the crossing-free line counts once.
    Open,
}

impl Problem {
    /// Every problem.
    pub const ALL: &[Problem] = &[Problem::Closed, Problem::Open];

    /// The JSON tag; `Meanders.Certify.Problem.tag` on the Lean side.
    pub fn tag(self) -> &'static str {
        match self {
            Problem::Closed => "closed",
            Problem::Open => "open",
        }
    }
}

impl fmt::Display for Problem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.tag())
    }
}

impl FromStr for Problem {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Problem::ALL
            .iter()
            .copied()
            .find(|p| p.tag() == s)
            .ok_or_else(|| {
                let known: Vec<_> = Problem::ALL.iter().map(|p| p.tag()).collect();
                format!("unknown problem {s:?}; known: {}", known.join(", "))
            })
    }
}
