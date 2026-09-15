//! Versioned run manifests. Commitments authenticate retained evidence; only
//! the Lean exact checker establishes a numerical claim.
use std::{
    fs,
    io::{self, BufWriter, Write},
    path::Path,
};

use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{Algorithm, Kind, first_crossing};
use crate::algorithms::first_crossing::optimized;
use crate::problem::Problem;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Profile {
    Full,
    Compact,
}

/// Optional file locations are transport hints, excluded from the commitment.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RunLayer {
    pub rows: usize,
    pub bytes: usize,
    #[serde(with = "natural_json")]
    pub ordinary: BigUint,
    #[serde(deserialize_with = "required_symmetric")]
    pub symmetric: Option<u128>,
    #[serde(
        default,
        rename = "lowerReturns",
        skip_serializing_if = "Option::is_none",
        with = "optional_natural_json"
    )]
    pub lower_returns: Option<BigUint>,
    pub sha256: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub file: Option<String>,
}

/// The historical `symmetric` key must be present (it is `null` for every
/// layer); a plain `Option` field would also accept its absence.
fn required_symmetric<'de, D: serde::Deserializer<'de>>(d: D) -> Result<Option<u128>, D::Error> {
    Option::deserialize(d)
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RunCertificate {
    pub kind: Kind,
    pub version: u32,
    pub profile: Profile,
    pub problem: Problem,
    pub algorithm: Algorithm,
    pub n: usize,
    #[serde(with = "natural_json")]
    pub count: BigUint,
    pub representation: String,
    pub layers: Vec<RunLayer>,
    pub root: String,
    #[serde(
        default,
        rename = "firstCrossing",
        skip_serializing_if = "Option::is_none"
    )]
    pub first_crossing: Option<first_crossing::Metadata>,
}

/// The wire format is a JSON natural, not BigUint's limb-array serde encoding.
/// `arbitrary_precision` keeps Number's original decimal text without an f64 hop.
pub(super) mod natural_json {
    use num_bigint::BigUint;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(value: &BigUint, serializer: S) -> Result<S::Ok, S::Error> {
        let number = value
            .to_string()
            .parse::<serde_json::Number>()
            .map_err(serde::ser::Error::custom)?;
        number.serialize(serializer)
    }

    /// Raw JSON text to a natural; anything but a digit string rejects.
    pub(super) fn parse<E: serde::de::Error>(
        raw: &serde_json::value::RawValue,
    ) -> Result<BigUint, E> {
        let text = raw.get();
        if !text.bytes().all(|b| b.is_ascii_digit()) {
            return Err(E::custom("expected a nonnegative JSON integer"));
        }
        text.parse().map_err(E::custom)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<BigUint, D::Error> {
        parse(&Box::<serde_json::value::RawValue>::deserialize(
            deserializer,
        )?)
    }
}

mod optional_natural_json {
    use num_bigint::BigUint;
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S: Serializer>(
        value: &Option<BigUint>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        match value {
            Some(value) => super::natural_json::serialize(value, serializer),
            None => serializer.serialize_none(),
        }
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Option<BigUint>, D::Error> {
        Option::<Box<serde_json::value::RawValue>>::deserialize(deserializer)?
            .map(|raw| super::natural_json::parse(&raw))
            .transpose()
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
pub fn sha256(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

/// RFC 9162 tree shape and domain separation, over canonical descriptor bytes.
fn merkle(leaves: &[Vec<u8>]) -> Vec<u8> {
    let mut h = Sha256::new();
    match leaves.len() {
        0 => {}
        1 => {
            h.update([0]);
            h.update(&leaves[0]);
        }
        n => {
            let k = 1usize << (usize::BITS - (n - 1).leading_zeros() - 1);
            h.update([1]);
            h.update(merkle(&leaves[..k]));
            h.update(merkle(&leaves[k..]));
        }
    }
    h.finalize().to_vec()
}

impl RunCertificate {
    #[cfg(test)]
    /// Parse exact JSON integer claims and validate their metadata and commitment.
    pub fn from_json(text: &str) -> Result<Self, serde_json::Error> {
        let run: Self = serde_json::from_str(text)?;
        run.validate()
            .map_err(<serde_json::Error as serde::de::Error>::custom)?;
        Ok(run)
    }

    /// Canonical ASCII descriptors are independent of JSON field ordering,
    /// locations and retention profile; full and compact share the same root.
    pub fn commitment(&self) -> String {
        let mut header = format!(
            "meanders-run-v1\n{}\n{}\n{}\n{}\n{}\n{}\n",
            self.problem,
            self.algorithm,
            self.n,
            self.count,
            self.representation,
            self.layers.len()
        );
        if let Some(metadata) = &self.first_crossing {
            metadata.append_header(&mut header);
        }
        let mut leaves = vec![header.into_bytes()];
        for (t, l) in self.layers.iter().enumerate() {
            let mut descriptor = format!(
                "layer\n{t}\n{}\n{}\n{}\n{}\n{}\n",
                l.rows,
                l.bytes,
                l.ordinary,
                l.symmetric.map_or_else(|| "-".into(), |x| x.to_string()),
                l.sha256
            );
            if let Some(lower) = &l.lower_returns {
                descriptor.push_str(&format!("lower-returns\n{lower}\n"));
            }
            leaves.push(descriptor.into_bytes());
        }
        hex(&merkle(&leaves))
    }

    #[cfg(test)]
    /// Validate the schema and commitment, without claiming numerical correctness.
    pub fn validate(&self) -> Result<(), String> {
        if self.version != 1 {
            return Err("unsupported run version".into());
        }
        let first_crossing_jet = self.algorithm.is_first_crossing()
            && self.representation == first_crossing::REPRESENTATION;
        let expected = if first_crossing_jet {
            first_crossing::REPRESENTATION
        } else {
            "count"
        };
        if self.representation != expected {
            return Err("incompatible run representation".into());
        }
        if self.first_crossing.is_some() != first_crossing_jet {
            return Err("incompatible First-Crossing metadata".into());
        }
        if expected == "count" {
            if self.profile != Profile::Compact || !self.layers.is_empty() {
                return Err("count requires compact profile and no layers".into());
            }
        } else if first_crossing_jet {
            self.first_crossing
                .as_ref()
                .expect("metadata presence checked")
                .validate(self)?;
        }
        let hex = |s: &str| {
            s.len() == 64
                && s.bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        };
        for l in &self.layers {
            if l.lower_returns.is_some() != first_crossing_jet {
                return Err("incompatible lower-return channel".into());
            }
            if !hex(&l.sha256) {
                return Err("invalid SHA-256 digest".into());
            }
            if l.symmetric.is_some() {
                return Err("incompatible layer channels".into());
            }
            if l.file.as_ref().is_some_and(String::is_empty)
                || (self.profile == Profile::Full && l.file.is_none())
            {
                return Err("full profile requires every layer file".into());
            }
        }
        if !hex(&self.root) || self.root != self.commitment() {
            return Err("run root mismatch".into());
        }
        Ok(())
    }

    /// Emit once per layer. Compact runs hash rows directly and write no
    /// payloads. `Ok(None)` means the evaluator declines the problem.
    pub fn produce(
        problem: Problem,
        algorithm: Algorithm,
        n: usize,
        profile: Profile,
        path: Option<&Path>,
        cfg: &optimized::Config,
    ) -> io::Result<Option<Self>> {
        if !algorithm.is_first_crossing() {
            if profile == Profile::Full {
                return Err(io::Error::other(
                    "full profile requires a layered evaluator and --out",
                ));
            }
            return Self::produce_count(problem, algorithm, n, cfg);
        }
        // Validate before any layer work so that bad inputs never write files.
        crate::algorithms::check_order(n, algorithm.evaluator().max_order(problem))
            .map_err(io::Error::other)?;
        if profile == Profile::Full && path.is_none() {
            return Err(io::Error::other(
                "full profile requires a layered evaluator and --out",
            ));
        }
        let mut cert = Self::skeleton(
            problem,
            algorithm,
            n,
            profile,
            first_crossing::REPRESENTATION,
        );
        first_crossing::produce(&mut cert, path, cfg.threads)?;
        cert.root = cert.commitment();
        Ok(Some(cert))
    }

    /// Count-only evidence: the compact `count` representation with no layers.
    pub fn produce_count(
        problem: Problem,
        algorithm: Algorithm,
        n: usize,
        cfg: &optimized::Config,
    ) -> io::Result<Option<Self>> {
        let count = algorithm
            .evaluator_with(*cfg)
            .count(problem, n)
            .map_err(io::Error::other)?;
        Ok(count.map(|count| Self::count_manifest(problem, algorithm, n, count)))
    }

    fn count_manifest(problem: Problem, algorithm: Algorithm, n: usize, count: BigUint) -> Self {
        let mut cert = Self::skeleton(problem, algorithm, n, Profile::Compact, "count");
        cert.count = count;
        cert.root = cert.commitment();
        cert
    }

    /// First-Crossing computes its joint outputs once, without layer callbacks.
    pub fn produce_all_count(
        algorithm: Algorithm,
        n: usize,
        cfg: &optimized::Config,
    ) -> io::Result<NativeRun> {
        let values = Self::native_values(algorithm, n).ok_or_else(|| {
            io::Error::other("--cert count requires a count-compatible native evaluator")
        })?;
        crate::algorithms::check_order(n, algorithm.evaluator().max_order(Problem::Closed))
            .map_err(io::Error::other)?;
        let counts =
            first_crossing::joint_counts(algorithm, n, cfg.threads).map_err(io::Error::other)?;
        let certificates = values
            .into_iter()
            .map(|(problem, index)| {
                let count =
                    first_crossing::select(problem, index, &counts.closed, &counts.open_even);
                Self::count_manifest(problem, algorithm, index, count.clone())
            })
            .collect();
        Ok(NativeRun {
            certificates,
            skipped: Vec::new(),
        })
    }

    /// The public values that one native run of `algorithm` at index `n`
    /// yields, primary first: the closed/open families share Closed(n),
    /// Open(2n) and Open(2n-1).
    /// Brute force has no native run and names its problem explicitly.
    pub fn native_values(algorithm: Algorithm, n: usize) -> Option<Vec<(Problem, usize)>> {
        match algorithm {
            Algorithm::BruteForce => None,
            Algorithm::FirstCrossing | Algorithm::FirstCrossingOptimized => {
                let mut values = vec![(Problem::Closed, n), (Problem::Open, 2 * n)];
                if n > 0 {
                    values.push((Problem::Open, 2 * n - 1));
                }
                Some(values)
            }
        }
    }

    /// Run the evaluator once at native index `n` and emit one manifest per
    /// public value it yields. Layered siblings share the primary run's layer
    /// descriptors and, for the full profile, its layer files, which are
    /// written as `n-<n>-layer-<t>.txt` inside `dir`. Values whose index
    /// exceeds the evaluator's maximum are listed in `skipped`.
    pub fn produce_all(
        algorithm: Algorithm,
        n: usize,
        profile: Profile,
        dir: Option<&Path>,
        cfg: &optimized::Config,
    ) -> io::Result<NativeRun> {
        let values = Self::native_values(algorithm, n).ok_or_else(|| {
            io::Error::other(format!("{algorithm} has no native run; name the problem"))
        })?;
        let mut run = NativeRun::default();
        let (primary_problem, _) = values[0];
        let path = dir.map(|d| d.join(format!("n-{n}.json")));
        let primary = Self::produce(primary_problem, algorithm, n, profile, path.as_deref(), cfg)?
            .ok_or_else(|| {
                io::Error::other(format!("{algorithm} does not handle {primary_problem}"))
            })?;
        let metadata = primary
            .first_crossing
            .as_ref()
            .expect("First-Crossing native metadata");
        for &(problem, index) in &values[1..] {
            if index > algorithm.evaluator().max_order(problem) {
                run.skipped.push((problem, index));
                continue;
            }
            let mut cert = primary.clone();
            cert.problem = problem;
            cert.n = index;
            cert.count =
                first_crossing::select(problem, index, &metadata.closed, &metadata.open_even)
                    .clone();
            cert.root = cert.commitment();
            run.certificates.push(cert);
        }
        run.certificates.insert(0, primary);
        Ok(run)
    }

    fn skeleton(
        problem: Problem,
        algorithm: Algorithm,
        n: usize,
        profile: Profile,
        representation: &str,
    ) -> Self {
        Self {
            kind: Kind::Run,
            version: 1,
            profile,
            problem,
            algorithm,
            n,
            count: BigUint::default(),
            representation: representation.into(),
            layers: Vec::new(),
            root: String::new(),
            first_crossing: None,
        }
    }
}

/// The manifests of one native run and the sibling values it could not emit.
#[derive(Debug, Default)]
pub struct NativeRun {
    pub certificates: Vec<RunCertificate>,
    pub skipped: Vec<(Problem, usize)>,
}

/// The layer file for layer `t` of the manifest at `manifest_path`, relative
/// to its directory: `<stem>-layer-<t>.txt`.
fn layer_file_name(manifest_path: &Path, t: usize) -> io::Result<String> {
    let stem = manifest_path
        .file_stem()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty())
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "{}: no file name to derive layer files from",
                    manifest_path.display()
                ),
            )
        })?;
    Ok(format!("{stem}-layer-{t}.txt"))
}

/// Write a lower-channel layer through a sink, so the producer can format
/// each row into a reused buffer instead of allocating a `String` per row.
pub(super) fn write_lower_layer_with(
    profile: Profile,
    path: Option<&Path>,
    t: usize,
    fill: impl FnOnce(&mut LayerSink) -> io::Result<()>,
) -> io::Result<RunLayer> {
    let mut sink = LayerSink::open(profile, path, t)?;
    fill(&mut sink)?;
    sink.finish()
}

/// One layer being written: optional payload file, running SHA-256 and the
/// descriptor summaries. Rows arrive as canonical bytes ending in LF.
pub(super) struct LayerSink {
    writer: Option<BufWriter<fs::File>>,
    layer: RunLayer,
    hash: Sha256,
}

impl LayerSink {
    fn open(profile: Profile, path: Option<&Path>, t: usize) -> io::Result<Self> {
        let file = if profile == Profile::Full {
            Some(layer_file_name(path.expect("full path prechecked"), t)?)
        } else {
            None
        };
        let writer = if let Some(file) = &file {
            Some(BufWriter::new(fs::File::create(
                path.expect("full path prechecked")
                    .parent()
                    .unwrap_or_else(|| Path::new(""))
                    .join(file),
            )?))
        } else {
            None
        };
        Ok(Self {
            writer,
            layer: RunLayer {
                rows: 0,
                bytes: 0,
                ordinary: BigUint::default(),
                symmetric: None,
                lower_returns: Some(BigUint::default()),
                sha256: String::new(),
                file,
            },
            hash: Sha256::new(),
        })
    }

    pub(super) fn row(
        &mut self,
        row: &[u8],
        ordinary: &BigUint,
        lower_returns: &BigUint,
    ) -> io::Result<()> {
        if let Some(w) = &mut self.writer {
            w.write_all(row)?;
        }
        self.hash.update(row);
        let layer = &mut self.layer;
        layer.rows = layer
            .rows
            .checked_add(1)
            .ok_or_else(|| io::Error::other("row count overflow"))?;
        layer.bytes = layer
            .bytes
            .checked_add(row.len())
            .ok_or_else(|| io::Error::other("byte count overflow"))?;
        layer.ordinary += ordinary;
        if let Some(sum) = &mut layer.lower_returns {
            *sum += lower_returns;
        }
        Ok(())
    }

    fn finish(mut self) -> io::Result<RunLayer> {
        if let Some(w) = &mut self.writer {
            w.flush()?;
        }
        self.layer.sha256 = hex(&self.hash.finalize());
        Ok(self.layer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn config() -> optimized::Config {
        optimized::Config::default()
    }

    #[test]
    fn native_values_follow_each_family() {
        assert_eq!(
            RunCertificate::native_values(Algorithm::BruteForce, 3),
            None
        );
        assert_eq!(
            RunCertificate::native_values(Algorithm::FirstCrossing, 4),
            Some(vec![
                (Problem::Closed, 4),
                (Problem::Open, 8),
                (Problem::Open, 7)
            ])
        );
    }

    #[test]
    fn produce_all_matches_single_problem_runs() {
        let cfg = config();
        for algorithm in [Algorithm::FirstCrossing, Algorithm::FirstCrossingOptimized] {
            for n in 0..=4 {
                let run = RunCertificate::produce_all(algorithm, n, Profile::Compact, None, &cfg)
                    .unwrap();
                assert!(run.skipped.is_empty(), "{algorithm} n={n}");
                let values = RunCertificate::native_values(algorithm, n).unwrap();
                assert_eq!(run.certificates.len(), values.len(), "{algorithm} n={n}");
                for (cert, &(problem, index)) in run.certificates.iter().zip(&values) {
                    assert_eq!((cert.problem, cert.n), (problem, index));
                    cert.validate().unwrap();
                    let single = RunCertificate::produce(
                        problem,
                        algorithm,
                        index,
                        Profile::Compact,
                        None,
                        &cfg,
                    )
                    .unwrap()
                    .unwrap();
                    assert_eq!(cert, &single, "{algorithm} {problem} {index}");
                }
            }
        }
    }

    #[test]
    fn produce_all_rejects_brute_force() {
        let cfg = config();
        let error =
            RunCertificate::produce_all(Algorithm::BruteForce, 2, Profile::Compact, None, &cfg)
                .unwrap_err();
        assert!(error.to_string().contains("no native run"), "{error}");
    }

    #[test]
    fn independent_hash_vectors() {
        let corpus: serde_json::Value = serde_json::from_str(include_str!(
            "../../../fixtures/certificates/sha256-vectors.json"
        ))
        .unwrap();
        for v in corpus["sha256"].as_array().unwrap() {
            assert_eq!(
                sha256(v["text"].as_str().unwrap().as_bytes()),
                v["sha256"].as_str().unwrap()
            );
        }
        for v in corpus["merkle"].as_array().unwrap() {
            let leaves: Vec<_> = v["leaves"]
                .as_array()
                .unwrap()
                .iter()
                .map(|s| s.as_str().unwrap().as_bytes().to_vec())
                .collect();
            assert_eq!(hex(&merkle(&leaves)), v["root"].as_str().unwrap());
        }
    }

    #[test]
    fn parser_validates_metadata_and_checked_horizons() {
        let base = RunCertificate::from_json(include_str!(
            "../../../fixtures/certificates/run/accept/closed-brute_force-3-compact.json"
        ))
        .unwrap();
        let reject = |mut c: RunCertificate, expected: &str| {
            c.root = c.commitment();
            let json = serde_json::to_string(&c).unwrap();
            let error = RunCertificate::from_json(&json).unwrap_err();
            assert!(error.to_string().contains(expected), "{error}");
        };
        let mut c = base.clone();
        c.version = 2;
        reject(c, "unsupported run version");
        let mut c = base.clone();
        c.profile = Profile::Full;
        reject(c, "count requires compact profile");
        let mut c = base;
        c.count += 1u32;
        let json = serde_json::to_string(&c).unwrap();
        assert!(
            RunCertificate::from_json(&json)
                .unwrap_err()
                .to_string()
                .contains("run root mismatch")
        );
    }

    #[test]
    fn large_counts_round_trip_without_float_conversion() {
        let mut c = RunCertificate {
            kind: Kind::Run,
            version: 1,
            profile: Profile::Compact,
            problem: Problem::Closed,
            algorithm: Algorithm::BruteForce,
            n: 1,
            count: BigUint::from(u128::MAX),
            representation: "count".into(),
            layers: Vec::new(),
            root: String::new(),
            first_crossing: None,
        };
        c.root = c.commitment();
        let json = serde_json::to_string(&c).unwrap();
        assert!(json.contains(&u128::MAX.to_string()));
        assert_eq!(RunCertificate::from_json(&json).unwrap(), c);
        for count in [
            BigUint::from(u128::MAX) + 1u32,
            (BigUint::from(1u32) << 1024) + 123u32,
        ] {
            c.count = count;
            c.root = c.commitment();
            let json = serde_json::to_string(&c).unwrap();
            assert!(json.contains(&format!("\"count\":{},", c.count)));
            assert_eq!(RunCertificate::from_json(&json).unwrap(), c);
        }
    }

    #[test]
    fn count_requires_a_json_natural() {
        let base = include_str!(
            "../../../fixtures/certificates/run/accept/closed-brute_force-3-compact.json"
        );
        for invalid in [
            "-1",
            "-0",
            "1.0",
            "1e3",
            "\"1\"",
            "null",
            "true",
            "[]",
            "{\"$serde_json::private::Number\":\"1\"}",
        ] {
            let text = base.replace("\"count\": 8", &format!("\"count\": {invalid}"));
            assert_ne!(text, base);
            // Deserialization itself must reject the type, before root validation.
            assert!(
                serde_json::from_str::<RunCertificate>(&text).is_err(),
                "{invalid}"
            );
        }
    }
}
