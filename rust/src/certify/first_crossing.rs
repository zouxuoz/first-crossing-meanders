//! Sector-major First-Crossing evidence with a separate lower-return moment.

use std::{fmt::Write as _, io, path::Path};

use num_bigint::BigUint;
use serde::{Deserialize, Serialize};

use crate::algorithms::first_crossing::{
    InputError, Parameters, Sector, Stage, optimized, reference,
};
use crate::problem::Problem;

use super::Algorithm;
use super::run::{RunCertificate, natural_json, write_lower_layer_with};

pub const REPRESENTATION: &str = "first-crossing-lower-jet";

/// The public value of one native pair: Open(2n) is the lower-return count,
/// Closed(n) and its odd alias Open(2n-1) the ordinary one.
pub(super) fn select<'a>(
    problem: Problem,
    index: usize,
    closed: &'a BigUint,
    open_even: &'a BigUint,
) -> &'a BigUint {
    if problem == Problem::Open && index.is_multiple_of(2) {
        open_even
    } else {
        closed
    }
}

/// The native index behind a public claim.
fn native_order(problem: Problem, n: usize) -> usize {
    match problem {
        Problem::Closed => n,
        Problem::Open => n.div_ceil(2),
    }
}

/// Both joint outputs of one native run, with no layer callbacks.
pub(super) fn joint_counts(
    algorithm: Algorithm,
    n: usize,
    threads: usize,
) -> Result<reference::Counts, InputError> {
    if algorithm == Algorithm::FirstCrossingOptimized {
        optimized::evaluate(n, optimized::Config { threads })
    } else {
        reference::evaluate(n)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum SectorIdentity {
    Low,
    High {
        cut: usize,
        upper: usize,
        lower: usize,
    },
}

impl From<Sector> for SectorIdentity {
    fn from(sector: Sector) -> Self {
        if sector.is_high() {
            let [upper, lower] = sector.cut_heights();
            Self::High {
                cut: sector.side_lengths()[0],
                upper,
                lower,
            }
        } else {
            Self::Low
        }
    }
}

impl SectorIdentity {
    #[cfg(test)]
    fn has_bonus(&self) -> bool {
        matches!(self, Self::High { lower, .. } if *lower > 0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct SectorSummary {
    pub sector: SectorIdentity,
    #[serde(with = "natural_json")]
    pub ordinary: BigUint,
    #[serde(with = "natural_json")]
    pub lower_returns: BigUint,
    #[serde(with = "natural_json")]
    pub bonus_contribution: BigUint,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Metadata {
    pub native_order: usize,
    pub threshold: usize,
    #[serde(with = "natural_json")]
    pub closed: BigUint,
    #[serde(with = "natural_json")]
    pub open_even: BigUint,
    pub sectors: Vec<SectorSummary>,
}

impl Metadata {
    /// Additional bytes in the existing header leaf, in complete sector order.
    pub(super) fn append_header(&self, header: &mut String) {
        write!(
            header,
            "first-crossing\n{}\n{}\n{}\n{}\n{}\n",
            self.native_order,
            self.threshold,
            self.closed,
            self.open_even,
            self.sectors.len()
        )
        .expect("write to string");
        for summary in &self.sectors {
            match summary.sector {
                SectorIdentity::Low => header.push_str("sector\nlow\n"),
                SectorIdentity::High { cut, upper, lower } => {
                    write!(header, "sector\nhigh\n{cut}\n{upper}\n{lower}\n")
                        .expect("write to string");
                }
            }
            write!(
                header,
                "{}\n{}\n{}\n",
                summary.ordinary, summary.lower_returns, summary.bonus_contribution
            )
            .expect("write to string");
        }
    }

    #[cfg(test)]
    /// Structural consistency only. The Lean layer checker verifies recurrence.
    pub(super) fn validate(&self, run: &RunCertificate) -> Result<(), String> {
        if self.native_order != native_order(run.problem, run.n) {
            return Err("First-Crossing native order mismatch".into());
        }
        if self.native_order == 0 {
            if self.threshold != 0
                || !self.sectors.is_empty()
                || !run.layers.is_empty()
                || self.closed != BigUint::default()
                || self.open_even != BigUint::from(1u32)
            {
                return Err("invalid First-Crossing zero convention".into());
            }
        } else {
            let parameters = Parameters::new(self.native_order, Some(self.threshold))
                .map_err(|e| e.to_string())?;
            let per_sector = self
                .native_order
                .checked_mul(2)
                .and_then(|n| n.checked_add(1))
                .ok_or("First-Crossing layer count exceeds usize")?;
            let total = per_sector
                .checked_mul(self.sectors.len())
                .ok_or("First-Crossing layer count exceeds usize")?;
            if self.sectors.is_empty() || total != run.layers.len() {
                return Err("wrong number of First-Crossing layers".into());
            }
            if !parameters
                .sectors()
                .map(SectorIdentity::from)
                .eq(self.sectors.iter().map(|s| s.sector.clone()))
            {
                return Err("First-Crossing sectors must be complete and ordered".into());
            }
            let mut closed = BigUint::default();
            let mut open_even = BigUint::default();
            for (i, summary) in self.sectors.iter().enumerate() {
                let terminal = &run.layers[(i + 1) * per_sector - 1];
                if terminal.ordinary != summary.ordinary
                    || terminal.lower_returns.as_ref() != Some(&summary.lower_returns)
                {
                    return Err("First-Crossing terminal summary mismatch".into());
                }
                let expected_bonus = if summary.sector.has_bonus() {
                    summary.ordinary.clone()
                } else {
                    BigUint::default()
                };
                if summary.bonus_contribution != expected_bonus {
                    return Err("First-Crossing terminal bonus mismatch".into());
                }
                closed += &summary.ordinary;
                open_even += &summary.lower_returns;
                open_even += &summary.bonus_contribution;
            }
            if self.closed != closed || self.open_even != open_even {
                return Err("First-Crossing aggregate mismatch".into());
            }
        }
        if &run.count != select(run.problem, run.n, &self.closed, &self.open_even) {
            return Err("First-Crossing public count mismatch".into());
        }
        Ok(())
    }
}

#[cfg(test)]
/// Existing native key order with explicit empty mate field and exact weights.
pub fn row_text(row: &reference::Row) -> String {
    let mut buffer = Vec::new();
    write_row(&mut buffer, row);
    String::from_utf8(buffer).expect("canonical rows are ASCII")
}

/// Append one canonical row, `counters|mates ordinary lowerReturns\n`, to
/// `buffer` after clearing it. Integers are written without allocation;
/// weights take a machine-word fast path and fall back to `BigUint` text.
pub fn write_row(buffer: &mut Vec<u8>, row: &reference::Row) {
    buffer.clear();
    push_list(buffer, &row.key.counters);
    buffer.push(b'|');
    push_list(buffer, &row.key.mate);
    buffer.push(b' ');
    push_weight(buffer, &row.weights.ordinary);
    buffer.push(b' ');
    push_weight(buffer, &row.weights.lower_returns);
    buffer.push(b'\n');
}

fn push_list(buffer: &mut Vec<u8>, values: &[usize]) {
    for (i, &value) in values.iter().enumerate() {
        if i > 0 {
            buffer.push(b',');
        }
        push_decimal(buffer, value as u128);
    }
}

fn push_weight(buffer: &mut Vec<u8>, value: &BigUint) {
    match u128::try_from(value) {
        Ok(small) => push_decimal(buffer, small),
        Err(_) => buffer.extend_from_slice(value.to_string().as_bytes()),
    }
}

fn push_decimal(buffer: &mut Vec<u8>, mut value: u128) {
    let mut digits = [0u8; 39];
    let mut at = digits.len();
    loop {
        at -= 1;
        digits[at] = b'0' + (value % 10) as u8;
        value /= 10;
        if value == 0 {
            break;
        }
    }
    buffer.extend_from_slice(&digits[at..]);
}

/// Stream each sector through the shared file/hash machinery, retaining summaries only.
pub(super) fn produce(
    run: &mut RunCertificate,
    path: Option<&Path>,
    threads: usize,
) -> io::Result<()> {
    let native_order = native_order(run.problem, run.n);
    let parameters = Parameters::new(native_order, None).map_err(io::Error::other)?;
    let mut sectors = Vec::new();
    let algorithm = run.algorithm;
    let mut buffer = Vec::with_capacity(256);
    let visit = |sector: Sector, stage: Stage, rows: &[reference::Row]| {
        let layer = write_lower_layer_with(run.profile, path, run.layers.len(), |sink| {
            for row in rows {
                write_row(&mut buffer, row);
                sink.row(&buffer, &row.weights.ordinary, &row.weights.lower_returns)?;
            }
            Ok(())
        })?;
        if stage.tick == sector.steps() {
            sectors.push(SectorSummary {
                sector: sector.into(),
                ordinary: layer.ordinary.clone(),
                lower_returns: layer.lower_returns.clone().expect("lower layer channel"),
                bonus_contribution: if sector.terminal_bonus() {
                    layer.ordinary.clone()
                } else {
                    BigUint::default()
                },
            });
        }
        run.layers.push(layer);
        Ok::<_, io::Error>(())
    };
    let counts = if algorithm == Algorithm::FirstCrossingOptimized {
        optimized::for_each_layer_with_config(parameters, optimized::Config { threads }, visit)?
    } else {
        reference::for_each_layer(parameters, visit)?
    };
    run.count = select(run.problem, run.n, &counts.closed, &counts.open_even).clone();
    run.first_crossing = Some(Metadata {
        native_order,
        threshold: parameters.threshold().unwrap_or(0),
        closed: counts.closed,
        open_even: counts.open_even,
        sectors,
    });
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algorithms::first_crossing::optimized;
    use crate::certify::Profile;

    fn produce(problem: Problem, n: usize) -> RunCertificate {
        RunCertificate::produce(
            problem,
            Algorithm::FirstCrossing,
            n,
            Profile::Compact,
            None,
            &optimized::Config::default(),
        )
        .unwrap()
        .unwrap()
    }

    #[test]
    fn packed_producer_has_identical_canonical_evidence() {
        for (problem, n) in [
            (Problem::Closed, 0),
            (Problem::Open, 0),
            (Problem::Closed, 5),
            (Problem::Open, 9),
            (Problem::Open, 10),
        ] {
            let expected = produce(problem, n);
            for threads in [1, 2, 3] {
                let mut actual = RunCertificate::produce(
                    problem,
                    Algorithm::FirstCrossingOptimized,
                    n,
                    Profile::Compact,
                    None,
                    &optimized::Config { threads },
                )
                .unwrap()
                .unwrap();
                actual.validate().unwrap();
                assert_eq!(actual.count, expected.count);
                assert_eq!(actual.layers, expected.layers);
                assert_eq!(actual.first_crossing, expected.first_crossing);
                // The producer tag is intentionally included in the root header.
                actual.algorithm = Algorithm::FirstCrossing;
                assert_eq!(actual.commitment(), expected.root);
            }
        }
    }

    #[test]
    fn zero_and_public_indices_use_one_pair() {
        for n in 0..=6 {
            for problem in [Problem::Closed, Problem::Open] {
                let run = produce(problem, n);
                run.validate().unwrap();
                let metadata = run.first_crossing.as_ref().unwrap();
                let expected = reference::evaluate(metadata.native_order).unwrap();
                assert_eq!(metadata.closed, expected.closed);
                assert_eq!(metadata.open_even, expected.open_even);
                assert_eq!(
                    RunCertificate::from_json(&serde_json::to_string(&run).unwrap()).unwrap(),
                    run
                );
                if n == 0 {
                    assert_eq!(metadata.threshold, 0);
                    assert!(metadata.sectors.is_empty());
                    assert!(run.layers.is_empty());
                }
            }
        }
    }

    #[test]
    fn canonical_row_and_header_bytes_are_explicit() {
        let row = reference::Row {
            key: crate::algorithms::first_crossing::Key {
                counters: [0; 4],
                mate: vec![],
            },
            weights: reference::Weights {
                ordinary: 1u32.into(),
                lower_returns: 0u32.into(),
            },
        };
        assert_eq!(row_text(&row), "0,0,0,0| 1 0\n");
        let metadata = Metadata {
            native_order: 1,
            threshold: 1,
            closed: 1u32.into(),
            open_even: 1u32.into(),
            sectors: vec![
                SectorSummary {
                    sector: SectorIdentity::Low,
                    ordinary: 0u32.into(),
                    lower_returns: 0u32.into(),
                    bonus_contribution: 0u32.into(),
                },
                SectorSummary {
                    sector: SectorIdentity::High {
                        cut: 1,
                        upper: 1,
                        lower: 1,
                    },
                    ordinary: 1u32.into(),
                    lower_returns: 0u32.into(),
                    bonus_contribution: 1u32.into(),
                },
            ],
        };
        let mut text = String::new();
        metadata.append_header(&mut text);
        assert_eq!(
            text,
            "first-crossing\n1\n1\n1\n1\n2\nsector\nlow\n0\n0\n0\nsector\nhigh\n1\n1\n1\n1\n0\n1\n"
        );
    }

    #[test]
    fn count_fixture_round_trips_with_its_root() {
        let text =
            include_str!("../../../fixtures/certificates/first-crossing/closed-3-count.json");
        let old = RunCertificate::from_json(text).unwrap();
        assert!(old.first_crossing.is_none());
        assert!(old.layers.is_empty());
        assert_eq!(old.representation, "count");
        assert_eq!(old.count, produce(Problem::Closed, 3).count);
        let serialized = serde_json::to_string_pretty(&old).unwrap();
        assert_eq!(serialized, text.trim_end());
    }

    #[test]
    fn pinned_lower_jet_fixtures_are_reproducible() {
        for text in [
            include_str!("../../../fixtures/certificates/first-crossing/closed-2-full.json"),
            include_str!("../../../fixtures/certificates/first-crossing/closed-2-compact.json"),
            include_str!("../../../fixtures/certificates/first-crossing/open-0-compact.json"),
            include_str!("../../../fixtures/certificates/first-crossing/open-2-full.json"),
        ] {
            let mut expected = RunCertificate::from_json(text).unwrap();
            for layer in &expected.layers {
                if let Some(file) = &layer.file {
                    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                        .join("../fixtures/certificates/first-crossing")
                        .join(file);
                    let bytes = std::fs::read(path).unwrap();
                    assert_eq!(bytes.len(), layer.bytes);
                    assert_eq!(crate::certify::run::sha256(&bytes), layer.sha256);
                }
            }
            expected.profile = Profile::Compact;
            for layer in &mut expected.layers {
                layer.file = None;
            }
            assert_eq!(produce(expected.problem, expected.n), expected);
        }
    }

    #[test]
    fn full_and_compact_share_canonical_bytes_and_root() {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory =
            std::env::temp_dir().join(format!("meanders-fc-{}-{nonce}", std::process::id()));
        std::fs::create_dir(&directory).unwrap();
        struct Cleanup(std::path::PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let _cleanup = Cleanup(directory.clone());
        for (problem, n) in [
            (Problem::Closed, 0),
            (Problem::Closed, 2),
            (Problem::Open, 4),
        ] {
            let path = directory.join(format!("{problem}-{n}.json"));
            let full = RunCertificate::produce(
                problem,
                Algorithm::FirstCrossing,
                n,
                Profile::Full,
                Some(&path),
                &optimized::Config::default(),
            )
            .unwrap()
            .unwrap();
            full.validate().unwrap();
            let compact = produce(problem, n);
            assert_eq!(full.root, compact.root);
            let mut stripped = full.clone();
            stripped.profile = Profile::Compact;
            for layer in &mut stripped.layers {
                layer.file = None;
            }
            assert_eq!(stripped, compact);
            let metadata = full.first_crossing.as_ref().unwrap();
            let parameters =
                Parameters::new(metadata.native_order, Some(metadata.threshold)).unwrap();
            let mut index = 0;
            reference::for_each_layer(parameters, |_, _, rows| {
                let layer = &full.layers[index];
                let bytes = std::fs::read(directory.join(layer.file.as_ref().unwrap())).unwrap();
                let expected = rows.iter().map(row_text).collect::<String>();
                assert_eq!(bytes, expected.as_bytes());
                assert_eq!(layer.rows, rows.len());
                assert_eq!(layer.bytes, bytes.len());
                assert_eq!(layer.sha256, crate::certify::run::sha256(&bytes));
                index += 1;
                Ok::<_, std::convert::Infallible>(())
            })
            .unwrap();
            assert_eq!(index, full.layers.len());
        }
    }

    #[test]
    fn layer_summaries_preserve_exact_values_above_u128() {
        let large: BigUint = (BigUint::from(1u32) << 1024) + 123u32;
        let layer = write_lower_layer_with(Profile::Compact, None, 0, |sink| {
            sink.row(b"arbitrary test bytes\n", &large, &large)?;
            sink.row(b"more test bytes\n", &large, &large)
        })
        .unwrap();
        assert_eq!(layer.ordinary, &large * 2u32);
        assert_eq!(layer.lower_returns, Some(&large * 2u32));
        assert_eq!(layer.symmetric, None);
        let text = serde_json::to_string(&layer).unwrap();
        assert_eq!(
            serde_json::from_str::<crate::certify::run::RunLayer>(&text).unwrap(),
            layer
        );
        assert!(text.contains(&format!("\"ordinary\":{}", &large * 2u32)));
        assert!(text.contains(&format!("\"lowerReturns\":{}", &large * 2u32)));
    }

    #[test]
    fn malformed_sector_metadata_is_rejected_even_with_a_fresh_root() {
        let base = produce(Problem::Closed, 3);
        let reject = |mut run: RunCertificate| {
            run.root = run.commitment();
            assert!(RunCertificate::from_json(&serde_json::to_string(&run).unwrap()).is_err());
        };
        let mut bad = base.clone();
        bad.first_crossing = None;
        reject(bad);
        let mut bad = base.clone();
        bad.first_crossing.as_mut().unwrap().native_order += 1;
        reject(bad);
        let mut bad = base.clone();
        bad.first_crossing.as_mut().unwrap().threshold = 0;
        reject(bad);
        let mut bad = base.clone();
        bad.first_crossing.as_mut().unwrap().sectors.swap(0, 1);
        reject(bad);
        let mut bad = base.clone();
        bad.first_crossing.as_mut().unwrap().sectors.pop();
        reject(bad);
        let mut bad = base.clone();
        bad.first_crossing.as_mut().unwrap().sectors[1].sector = SectorIdentity::Low;
        reject(bad);
        let mut bad = base.clone();
        bad.first_crossing.as_mut().unwrap().sectors[0].ordinary += 1u32;
        reject(bad);
        let mut bad = base.clone();
        bad.first_crossing.as_mut().unwrap().sectors[0].lower_returns += 1u32;
        reject(bad);
        let mut bad = base.clone();
        bad.first_crossing.as_mut().unwrap().sectors[0].bonus_contribution += 1u32;
        reject(bad);
        let mut bad = base.clone();
        bad.first_crossing.as_mut().unwrap().closed += 1u32;
        reject(bad);
        let mut bad = base.clone();
        bad.first_crossing.as_mut().unwrap().open_even += 1u32;
        reject(bad);
        let mut bad = base.clone();
        bad.count += 1u32;
        reject(bad);
        let mut bad = base.clone();
        bad.layers[0].lower_returns = None;
        reject(bad);
        let mut bad = base.clone();
        bad.layers[0].symmetric = Some(0);
        reject(bad);
        let mut bad = base.clone();
        bad.representation = "count".into();
        reject(bad);
    }

    #[test]
    fn extension_naturals_reject_noninteger_json() {
        let run = produce(Problem::Closed, 1);
        let text = serde_json::to_string(&run).unwrap();
        for field in [
            "ordinary",
            "lowerReturns",
            "bonusContribution",
            "closed",
            "openEven",
        ] {
            for invalid in ["-1", "-0", "1.0", "1e3", "\"1\"", "true", "[]"] {
                let mut value: serde_json::Value = serde_json::from_str(&text).unwrap();
                let target = if ["closed", "openEven"].contains(&field) {
                    &mut value["firstCrossing"][field]
                } else {
                    &mut value["firstCrossing"]["sectors"][0][field]
                };
                *target = serde_json::Value::String("__INVALID_NATURAL__".into());
                let malformed = serde_json::to_string(&value)
                    .unwrap()
                    .replace("\"__INVALID_NATURAL__\"", invalid);
                assert!(
                    serde_json::from_str::<RunCertificate>(&malformed).is_err(),
                    "{field} {invalid}"
                );
            }
        }
    }
}
