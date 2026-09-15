//! Fast, unverified meander evaluators and the certificates they emit.
//!
//! Nothing here is trusted: a count is believed only once `lake exe verify`
//! has accepted the certificate. `ARCHITECTURE.md` at the repository root
//! describes how this crate mirrors the Lean layers.

mod algorithms;
mod certify;
mod problem;
#[cfg(test)]
mod test_support;

use std::fs;
use std::path::Path;
use std::process::ExitCode;
use std::str::FromStr;

use clap::{Parser, ValueEnum};
use num_bigint::BigUint;

use crate::algorithms::first_crossing::optimized;
use crate::certify::{Algorithm, NativeRun, Profile, RunCertificate};
use crate::problem::Problem;

/// `--problem` accepts every problem tag, or `all` for every public value
/// of one native run.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum ProblemArg {
    One(Problem),
    All,
}

impl FromStr for ProblemArg {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "all" {
            Ok(ProblemArg::All)
        } else {
            Problem::from_str(s)
                .map(ProblemArg::One)
                .map_err(|e| format!("{e}, all"))
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, ValueEnum)]
enum CertKind {
    /// Full through order 8 for the First-Crossing evaluators, compact otherwise.
    Auto,
    /// Retain all canonical layers next to the manifest; requires --out.
    Full,
    /// Retain commitments and summaries, regenerate omitted layers in Lean.
    Compact,
    /// Emit a compact count claim without layer commitments.
    Count,
}

impl CertKind {
    fn profile(self, algorithm: Algorithm, n: usize) -> Profile {
        match self {
            CertKind::Auto if n <= 8 && algorithm.is_first_crossing() => Profile::Full,
            CertKind::Full => Profile::Full,
            _ => Profile::Compact,
        }
    }
}

/// Count meanders and emit a certificate for the Lean checker to verify.
#[derive(Parser, Debug)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(clap::Subcommand, Debug)]
enum Command {
    /// Count the meanders of a given order.
    Count {
        /// Which problem to count, by its certificate tag, or `all`: run the
        /// evaluator once at its native index and write one manifest per
        /// public value (Closed(n), Open(2n) and Open(2n-1) for the
        /// First-Crossing evaluators). `all` requires
        /// `--out` naming a directory and is rejected for `brute_force`.
        #[arg(long, default_value = "closed")]
        problem: ProblemArg,

        /// Closed order, or the genuine crossing count for open meanders.
        #[arg(long)]
        n: usize,

        /// Which evaluator to run, by its certificate tag.
        #[arg(long, default_value = "brute_force")]
        algorithm: Algorithm,

        /// Evidence selection: full/compact layers, or a count-only claim.
        #[arg(long, value_enum, default_value = "auto")]
        cert: CertKind,

        /// Where to write the certificate JSON; prints to stdout if omitted.
        /// A full run's layer files go next to it as
        /// `<stem>-layer-<t>.txt`. With `--problem all` this is a directory
        /// receiving `<problem>-<n>-<profile>.json` manifests that share
        /// `n-<n>-layer-<t>.txt` layer files.
        #[arg(long)]
        out: Option<String>,

        /// Threads for first_crossing_optimized; `0` uses its default of one.
        #[arg(long, default_value_t = 0)]
        threads: usize,

        /// Exact answer check for a single problem; nothing is written on a
        /// mismatch. Useful in measured runs.
        #[arg(long)]
        expected: Option<BigUint>,
    },
}

fn main() -> ExitCode {
    let Command::Count {
        problem,
        n,
        algorithm,
        cert,
        out,
        threads,
        expected,
    } = Cli::parse().command;
    match count(
        problem,
        n,
        algorithm,
        cert,
        out.as_deref(),
        threads,
        expected,
    ) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("error: {message}");
            ExitCode::FAILURE
        }
    }
}

/// One run, single-problem or `all`.
fn count(
    problem: ProblemArg,
    n: usize,
    algorithm: Algorithm,
    cert: CertKind,
    out: Option<&str>,
    threads: usize,
    expected: Option<BigUint>,
) -> Result<(), String> {
    if threads != 0 && algorithm != Algorithm::FirstCrossingOptimized {
        return Err("--threads applies to first_crossing_optimized only".into());
    }
    let cfg = optimized::Config {
        threads: if threads == 0 {
            optimized::Config::default().threads
        } else {
            threads
        },
    };
    let profile = cert.profile(algorithm, n);
    match problem {
        ProblemArg::One(problem) => {
            let path = out.map(Path::new);
            let production = if cert == CertKind::Count {
                RunCertificate::produce_count(problem, algorithm, n, &cfg)
            } else {
                RunCertificate::produce(problem, algorithm, n, profile, path, &cfg)
            };
            let certificate = production
                .map_err(|e| format!("producing run: {e}"))?
                .ok_or_else(|| format!("{algorithm} does not handle the problem {problem}"))?;
            if expected.is_some_and(|expected| expected != certificate.count) {
                return Err(format!("incorrect result: {}", certificate.count));
            }
            let json = to_json(&certificate);
            match path {
                Some(path) => write(path, json),
                None => {
                    println!("{json}");
                    Ok(())
                }
            }
        }
        ProblemArg::All => {
            if expected.is_some() {
                return Err("--expected applies to a single problem only".into());
            }
            let dir = Path::new(out.ok_or("--problem all requires --out naming a directory")?);
            if RunCertificate::native_values(algorithm, n).is_none() {
                return Err(format!("{algorithm} has no native run; name the problem"));
            }
            fs::create_dir_all(dir).map_err(|e| format!("creating {}: {e}", dir.display()))?;
            let run = if cert == CertKind::Count {
                RunCertificate::produce_all_count(algorithm, n, &cfg)
            } else {
                RunCertificate::produce_all(algorithm, n, profile, Some(dir), &cfg)
            }
            .map_err(|e| format!("producing run: {e}"))?;
            write_all(dir, algorithm, &run)
        }
    }
}

/// One `<problem>-<n>-<profile>.json` per manifest in `dir`, printing
/// `<problem> <n> <count> <path>` for each.
fn write_all(dir: &Path, algorithm: Algorithm, run: &NativeRun) -> Result<(), String> {
    for (problem, index) in &run.skipped {
        eprintln!(
            "note: {problem} {index} exceeds the {algorithm} maximum {}; not emitted",
            algorithm.evaluator().max_order(*problem)
        );
    }
    for certificate in &run.certificates {
        let tag = match certificate.profile {
            Profile::Full => "full",
            Profile::Compact => "compact",
        };
        let path = dir.join(format!(
            "{}-{}-{tag}.json",
            certificate.problem, certificate.n
        ));
        write(&path, to_json(certificate))?;
        println!(
            "{} {} {} {}",
            certificate.problem,
            certificate.n,
            certificate.count,
            path.display()
        );
    }
    Ok(())
}

fn to_json(certificate: &RunCertificate) -> String {
    serde_json::to_string_pretty(certificate).expect("certificate serializes")
}

fn write(path: &Path, json: String) -> Result<(), String> {
    fs::write(path, json).map_err(|e| format!("writing {}: {e}", path.display()))
}
