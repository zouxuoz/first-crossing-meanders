//! The First-Crossing CLI as its callers see it: the emitted manifest JSON.
//! Structure and commitments are checked by the Lean verifier and the
//! crate's own producer tests; here only the public fields are read.

use std::process::{Command, Output};

use serde_json::Value;

fn run(problem: &str, n: usize, extra: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_meanders"))
        .args([
            "count",
            "--algorithm",
            "first_crossing",
            "--problem",
            problem,
            "--n",
            &n.to_string(),
        ])
        .args(extra)
        .output()
        .expect("run First-Crossing CLI")
}

fn manifest(output: &Output) -> Value {
    assert!(output.status.success(), "{output:?}");
    serde_json::from_slice(&output.stdout).expect("manifest JSON")
}

#[test]
fn cli_emits_sector_lower_jet_for_closed_and_open() {
    for (problem, n, count) in [
        ("closed", 0, "0"),
        ("open", 0, "1"),
        ("closed", 3, "8"),
        ("open", 5, "8"),
        ("open", 6, "14"),
    ] {
        let cert = manifest(&run(problem, n, &["--cert", "compact"]));
        assert_eq!(cert["algorithm"], "first_crossing");
        assert_eq!(cert["problem"], problem);
        assert_eq!(cert["n"], n);
        assert_eq!(cert["profile"], "compact");
        assert_eq!(cert["representation"], "first-crossing-lower-jet");
        assert!(cert["firstCrossing"].is_object());
        assert_eq!(cert["layers"].as_array().unwrap().is_empty(), n == 0);
        assert_eq!(cert["count"].to_string(), count);
    }
}

#[test]
fn cli_rejects_unsupported_inputs_without_a_certificate() {
    for (problem, n, extra, message) in [
        ("unknown", usize::MAX, &[][..], "unknown problem"),
        ("closed", usize::MAX, &[][..], "exceeds evaluator maximum"),
        ("open", usize::MAX, &[][..], "exceeds evaluator maximum"),
        (
            "closed",
            1,
            &["--cert", "full"][..],
            "requires a layered evaluator",
        ),
        ("closed", 1, &["--threads", "2"][..], "--threads applies"),
        (
            "closed",
            3,
            &["--cert", "count", "--expected", "9"][..],
            "incorrect result: 8",
        ),
    ] {
        let result = run(problem, n, extra);
        assert!(!result.status.success(), "{result:?}");
        assert!(result.stdout.is_empty(), "{result:?}");
        assert!(
            String::from_utf8_lossy(&result.stderr).contains(message),
            "{result:?}"
        );
    }
}

#[test]
fn expected_count_passes_a_correct_claim_through() {
    let cert = manifest(&run("closed", 3, &["--cert", "count", "--expected", "8"]));
    assert_eq!(cert["representation"], "count");
    assert_eq!(cert["count"].to_string(), "8");
}

#[test]
fn optimized_cli_accepts_bounded_worker_count() {
    let result = Command::new(env!("CARGO_BIN_EXE_meanders"))
        .args([
            "count",
            "--algorithm",
            "first_crossing_optimized",
            "--problem",
            "open",
            "--n",
            "10",
            "--threads",
            "2",
            "--cert",
            "compact",
        ])
        .output()
        .unwrap();
    let cert = manifest(&result);
    assert_eq!(cert["algorithm"], "first_crossing_optimized");
    assert_eq!(cert["representation"], "first-crossing-lower-jet");
    assert_eq!(cert["count"].to_string(), "538");
}

/// Worker requests above the former limit of 64 are accepted and exact.
#[test]
fn optimized_cli_accepts_large_worker_counts() {
    for threads in ["96", "128"] {
        let result = Command::new(env!("CARGO_BIN_EXE_meanders"))
            .args([
                "count",
                "--algorithm",
                "first_crossing_optimized",
                "--problem",
                "closed",
                "--n",
                "9",
                "--threads",
                threads,
                "--cert",
                "count",
            ])
            .output()
            .unwrap();
        let cert = manifest(&result);
        assert_eq!(cert["algorithm"], "first_crossing_optimized");
        assert_eq!(cert["count"].to_string(), "933458", "threads={threads}");
    }
}
