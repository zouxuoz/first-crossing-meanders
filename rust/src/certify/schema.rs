//! The certificate schema, mirrored in `Meanders/Certify/Schema.lean`.
//!
//! Tags are serialized from these enumerations so they can never be
//! misspelled here; the fixtures in `fixtures/certificates/run/accept/` are what
//! keep the two sides in agreement.

use std::fmt;
use std::str::FromStr;

use serde::{Deserialize, Serialize};

use crate::algorithms::{Evaluator, brute_force, first_crossing};

/// Which evaluator produced a certificate. Serialized as the `algorithm`
/// field the Lean verifier dispatches on. Mirrors `Meanders.Certify.Algorithm`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Algorithm {
    BruteForce,
    /// Shared first-crossing carrier with ordinary and lower-return weights.
    FirstCrossing,
    /// Packed first-crossing layers; the same shared reference recurrence.
    FirstCrossingOptimized,
}

impl Algorithm {
    /// Every registered evaluator.
    pub const ALL: &[Algorithm] = &[
        Algorithm::BruteForce,
        Algorithm::FirstCrossing,
        Algorithm::FirstCrossingOptimized,
    ];

    /// The JSON tag; `Meanders.Certify.Algorithm.tag` on the Lean side.
    pub fn tag(self) -> &'static str {
        match self {
            Algorithm::FirstCrossing => "first_crossing",
            Algorithm::FirstCrossingOptimized => "first_crossing_optimized",
            Algorithm::BruteForce => "brute_force",
        }
    }

    /// Both First-Crossing producers share the same proved recurrence and
    /// row semantics; `Meanders.Certify.Algorithm.isFirstCrossing` on the Lean side.
    pub fn is_first_crossing(self) -> bool {
        matches!(
            self,
            Algorithm::FirstCrossing | Algorithm::FirstCrossingOptimized
        )
    }

    /// The implementation behind the tag: the registry, at its default of
    /// one worker.
    pub fn evaluator(self) -> &'static dyn Evaluator {
        match self {
            Algorithm::FirstCrossing => &first_crossing::reference::FirstCrossing,
            Algorithm::FirstCrossingOptimized => {
                &first_crossing::optimized::FirstCrossingOptimized {
                    config: first_crossing::optimized::Config { threads: 1 },
                }
            }
            Algorithm::BruteForce => &brute_force::BruteForce,
        }
    }

    /// The registry with a worker count. Only `first_crossing_optimized`
    /// reads it; the others are their one-worker registry entries.
    pub fn evaluator_with(self, config: first_crossing::optimized::Config) -> Box<dyn Evaluator> {
        match self {
            Algorithm::FirstCrossingOptimized => {
                Box::new(first_crossing::optimized::FirstCrossingOptimized { config })
            }
            _ => Box::new(self.evaluator()),
        }
    }
}

impl fmt::Display for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.tag())
    }
}

impl FromStr for Algorithm {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Algorithm::ALL
            .iter()
            .copied()
            .find(|a| a.tag() == s)
            .ok_or_else(|| {
                let known: Vec<_> = Algorithm::ALL.iter().map(|a| a.tag()).collect();
                format!("unknown algorithm {s:?}; known: {}", known.join(", "))
            })
    }
}

/// The `kind` tag of the one on-disk certificate format; serde rejects any
/// other value, as `Meanders.Certify.parseJson` does on the Lean side.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Kind {
    Run,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::certify::RunCertificate;
    use crate::problem::Problem;
    use std::fs;
    use std::path::PathBuf;

    /// The `.json` files of one fixture directory under `fixtures/certificates/`,
    /// as `(relative name, path, text)`. Every directory must be non-empty.
    fn fixtures(sub: &str) -> Vec<(String, PathBuf, String)> {
        let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../fixtures/certificates")
            .join(sub);
        let mut out: Vec<_> = fs::read_dir(&dir)
            .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
            .map(|e| e.expect("entry").path())
            .filter(|p| p.extension().is_some_and(|x| x == "json"))
            .map(|p| {
                let name = format!("{sub}/{}", p.file_name().unwrap().to_string_lossy());
                let text = fs::read_to_string(&p).expect("fixture is readable");
                (name, p, text)
            })
            .collect();
        out.sort();
        assert!(!out.is_empty(), "no fixtures in {}", dir.display());
        out
    }

    #[test]
    fn serde_tags_agree_with_tag() {
        for &a in Algorithm::ALL {
            assert_eq!(serde_json::to_value(a).unwrap(), serde_json::json!(a.tag()));
            assert_eq!(a.tag().parse::<Algorithm>().unwrap(), a);
        }
        assert!("unknown".parse::<Algorithm>().is_err());
        assert!(serde_json::from_str::<Algorithm>("\"unknown\"").is_err());
        assert_eq!(
            serde_json::to_value(Kind::Run).unwrap(),
            serde_json::json!("run")
        );
        assert!(serde_json::from_str::<Kind>("\"proof\"").is_err());
        for &p in Problem::ALL {
            assert_eq!(serde_json::to_value(p).unwrap(), serde_json::json!(p.tag()));
            assert_eq!(p.tag().parse::<Problem>().unwrap(), p);
        }
        assert!("unknown".parse::<Problem>().is_err());
    }

    /// Every evaluator answers every problem it claims to, or says so.
    #[test]
    fn evaluators_answer_or_decline() {
        for &a in Algorithm::ALL {
            for &p in Problem::ALL {
                assert_eq!(
                    a.evaluator().count(p, 1),
                    Ok(Some(1u32.into())),
                    "{a} for {p}"
                );
            }
        }
    }

    #[test]
    fn evaluators_reject_invalid_supported_inputs_before_execution() {
        use crate::algorithms::EvalError;
        for &a in Algorithm::ALL {
            let evaluator = a.evaluator();
            for &p in Problem::ALL {
                let supported = evaluator.count(p, 0).unwrap().is_some();
                for n in [evaluator.max_order(p) + 1, usize::MAX] {
                    let expected = if supported {
                        Err(EvalError::OrderExceeded {
                            n,
                            max: evaluator.max_order(p),
                        })
                    } else {
                        Ok(None)
                    };
                    assert_eq!(evaluator.count(p, n), expected, "{a} {p} {n}");
                }
            }
        }
    }

    /// Run fixtures round-trip, agree with the evaluator and retain their payload bytes.
    #[test]
    fn accept_fixtures_parse_and_hold() {
        for (name, path, text) in fixtures("run/accept") {
            let c = RunCertificate::from_json(&text).unwrap_or_else(|e| panic!("{name}: {e}"));
            assert!(c.n <= 7, "fixtures must stay small");
            assert_eq!(
                c.algorithm.evaluator().count(c.problem, c.n),
                Ok(Some(c.count.clone())),
                "{name}"
            );
            for l in &c.layers {
                if let Some(file) = &l.file {
                    let bytes = fs::read(path.parent().unwrap().join(file)).unwrap();
                    assert_eq!(bytes.len(), l.bytes, "{name}");
                    assert_eq!(super::super::run::sha256(&bytes), l.sha256, "{name}");
                }
            }
            let json = serde_json::to_string(&c).unwrap();
            assert_eq!(RunCertificate::from_json(&json).unwrap(), c);
        }
    }

    /// Accepted fixtures are reproduced exactly: the root binds the header,
    /// summaries and canonical payload bytes.
    #[test]
    fn producer_reproduces_accepted_fixtures() {
        use crate::algorithms::first_crossing::optimized;
        use crate::certify::Profile;
        let config = optimized::Config { threads: 2 };
        for (name, _, text) in fixtures("run/accept") {
            let mut expected = RunCertificate::from_json(&text).unwrap();
            let actual = RunCertificate::produce(
                expected.problem,
                expected.algorithm,
                expected.n,
                Profile::Compact,
                None,
                &config,
            )
            .unwrap()
            .unwrap();
            expected.profile = Profile::Compact;
            for layer in &mut expected.layers {
                layer.file = None;
            }
            assert_eq!(actual, expected, "{name}");
        }
    }

    #[test]
    fn malformed_formats_are_rejected() {
        assert!(
            RunCertificate::from_json(include_str!(
                "../../../fixtures/certificates/run/reject/claim-unknown-algorithm.json"
            ))
            .unwrap_err()
            .to_string()
            .contains("unknown variant `unknown`")
        );
        for (name, _, text) in fixtures("reject") {
            assert!(RunCertificate::from_json(&text).is_err(), "{name}");
        }
    }

    #[test]
    fn duplicate_fields_are_rejected_by_rust() {
        #[derive(Deserialize)]
        struct Case {
            name: String,
            text: String,
        }
        let cases: Vec<Case> = serde_json::from_str(include_str!(
            "../../../fixtures/certificates/json-duplicates.json"
        ))
        .unwrap();
        assert!(!cases.is_empty());
        for c in cases {
            let error = RunCertificate::from_json(&c.text).unwrap_err();
            assert!(
                error.to_string().contains("duplicate field"),
                "{}: {error}",
                c.name
            );
        }
    }
}
