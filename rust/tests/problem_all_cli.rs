//! `--problem all`: one native run, one manifest per public value. Only the
//! public JSON fields are read here; the Lean verifier checks the rest.

use std::fs;
use std::path::Path;
use std::process::{Command, Output};

use serde_json::Value;

fn run(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_meanders"))
        .arg("count")
        .args(args)
        .output()
        .expect("run CLI")
}

fn temp_dir(name: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("meanders-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    dir
}

fn manifest(path: &Path) -> Value {
    serde_json::from_str(&fs::read_to_string(path).unwrap()).expect("manifest JSON")
}

#[test]
fn all_writes_one_manifest_per_public_value() {
    let dir = temp_dir("all-fc");
    let n = "3";
    let out = run(&[
        "--problem",
        "all",
        "--algorithm",
        "first_crossing",
        "--n",
        n,
        "--out",
        dir.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{out:?}");
    let stdout = String::from_utf8(out.stdout).unwrap();
    let lines: Vec<_> = stdout.lines().collect();
    assert_eq!(lines.len(), 3, "{stdout}");
    for (line, expected) in lines.iter().zip(["closed 3 8", "open 6 14", "open 5 8"]) {
        assert!(line.starts_with(expected), "{line}");
    }
    let mut names: Vec<_> = fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .filter(|name| name.ends_with(".json"))
        .collect();
    names.sort();
    assert_eq!(
        names,
        ["closed-3-full.json", "open-5-full.json", "open-6-full.json"]
    );
    for name in names {
        let cert = manifest(&dir.join(&name));
        assert_eq!(cert["profile"], "full");
        let layers = cert["layers"].as_array().unwrap();
        assert!(!layers.is_empty());
        for layer in layers {
            assert!(dir.join(layer["file"].as_str().unwrap()).is_file());
        }
    }
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn all_rejects_missing_out_brute_force_unknown_problems_and_expected() {
    for (args, message) in [
        (
            &[
                "--problem",
                "all",
                "--algorithm",
                "brute_force",
                "--n",
                "2",
                "--out",
                "/tmp/x",
            ][..],
            "no native run",
        ),
        (
            &["--problem", "nope", "--n", "2"][..],
            "known: closed, open, all",
        ),
        (
            &[
                "--problem",
                "all",
                "--algorithm",
                "first_crossing",
                "--n",
                "2",
                "--out",
                "/tmp/x",
                "--expected",
                "2",
            ][..],
            "--expected applies to a single problem",
        ),
    ] {
        let out = run(args);
        assert!(!out.status.success(), "{args:?}");
        let stderr = String::from_utf8(out.stderr).unwrap();
        assert!(stderr.contains(message), "{stderr}");
    }
}

#[test]
fn count_only_first_crossing_matches_single_runs_and_known_values() {
    for algorithm in ["first_crossing", "first_crossing_optimized"] {
        for n in [0, 3] {
            let dir = temp_dir(&format!("count-{algorithm}-{n}"));
            let mut args = vec![
                "--problem",
                "all",
                "--algorithm",
                algorithm,
                "--cert",
                "count",
                "--n",
                if n == 0 { "0" } else { "3" },
                "--out",
                dir.to_str().unwrap(),
            ];
            if algorithm == "first_crossing_optimized" {
                args.extend(["--threads", "3"]);
            }
            let out = run(&args);
            assert!(out.status.success(), "{out:?}");
            let entries: Vec<_> = fs::read_dir(&dir).unwrap().collect();
            assert_eq!(entries.len(), if n == 0 { 2 } else { 3 });
            for entry in entries {
                let cert = manifest(&entry.unwrap().path());
                assert_eq!(cert["representation"], "count");
                assert_eq!(cert["profile"], "compact");
                assert!(cert["layers"].as_array().unwrap().is_empty());
                assert!(cert.get("firstCrossing").is_none());
                let problem = cert["problem"].as_str().unwrap();
                let index = cert["n"].as_u64().unwrap();
                let expected = match (problem, index) {
                    ("closed", 0) => "0",
                    ("open", 0) => "1",
                    ("open", 6) => "14",
                    _ => "8",
                };
                assert_eq!(cert["count"].to_string(), expected);
                let index = index.to_string();
                let single = run(&[
                    "--problem",
                    problem,
                    "--algorithm",
                    algorithm,
                    "--n",
                    &index,
                    "--cert",
                    "count",
                ]);
                assert!(single.status.success(), "{single:?}");
                let single: Value = serde_json::from_slice(&single.stdout).unwrap();
                assert_eq!(single["root"], cert["root"]);
            }
            fs::remove_dir_all(dir).unwrap();
        }
    }
}
