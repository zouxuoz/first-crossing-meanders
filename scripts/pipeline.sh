#!/usr/bin/env bash
# Runs the Rust -> certificate -> Lean pipeline. Every certificate the Rust
# CLI emits at small orders must be accepted by the Lean verifier, every
# evaluator must agree with every other and with fixtures/oeis, and the
# fixtures in fixtures/certificates/ must be accepted or rejected as their
# directory says. The Rust tests check the same fixtures from the other side.
#
# scripts/pipeline_matrix.py holds the evaluator/order matrix and the
# cross-checks; scripts/test_run_certificates.py and
# scripts/test_first_crossing_certificates.py hold the forgery, retention
# and CLI contracts.
set -euo pipefail
shopt -s nullglob

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORK_DIR="$(mktemp -d)"
trap 'rm -rf "$WORK_DIR"' EXIT

echo "==> Building Rust CLI"
# Release: brute force is catalan(n)^2 walks, and a debug build is ~20x slower.
cargo build --release --manifest-path "$ROOT_DIR/rust/Cargo.toml"
export MEANDERS_BIN="$ROOT_DIR/rust/target/release/meanders"

echo "==> Building Lean verifier"
(cd "$ROOT_DIR" && lake build verify)
export VERIFY_BIN="$ROOT_DIR/.lake/build/bin/verify"

# include_str data is not a Lake module dependency: rerun the shared grammar
# corpus and verifier guards even when their cached module is up to date.
for module in Verifier Run FirstCrossingCertificates; do
  (cd "$ROOT_DIR" && lake env lean "MeandersTests/$module.lean")
done

status=0
expect() { # expect <accept|reject> <certificate> <label>
  local want=$1 cert=$2 label=$3 got output code
  if output=$("$VERIFY_BIN" "$cert" 2>"$WORK_DIR/verify.err"); then code=0; else code=$?; fi
  case "$code:$output" in
    '0:ACCEPT: '*) got=accept ;;
    '1:REJECT: '*) got=reject ;;
    *) got=error ;;
  esac
  # IO error reasons may span lines; a second report marker is an error.
  if [[ -s "$WORK_DIR/verify.err" ||
        "$output" == *$'\nACCEPT: '* || "$output" == *$'\nREJECT: '* ]]; then got=error; fi
  if [[ $got == "$want" ]]; then
    echo "    ok ($got): $label"
  else
    echo "    FAIL (want $want, got $got): $label" >&2
    printf '    exit %s: %s\n' "$code" "$output" >&2
    cat "$WORK_DIR/verify.err" >&2
    status=1
  fi
}

echo "==> Unreadable top-level certificates report controlled failures"
expect reject "$WORK_DIR/missing-manifest.json" "missing manifest"
expect reject "$WORK_DIR" "directory as manifest"

echo "==> Every evaluator's certificates must be accepted and agree (scripts/pipeline_matrix.py)"
if ! python3 "$ROOT_DIR/scripts/pipeline_matrix.py"; then status=1; fi

FIXTURES="$ROOT_DIR/fixtures/certificates"

echo "==> First-Crossing count-only native runs must be accepted"
for algorithm in first_crossing first_crossing_optimized; do
  for n in 0 3; do
    "$MEANDERS_BIN" count --problem all --algorithm "$algorithm" --n "$n" --cert count --out "$WORK_DIR/count-only"
    for manifest in "$WORK_DIR"/count-only/*.json; do
      expect accept "$manifest" "$algorithm count-only n=$n"
    done
    rm -rf "$WORK_DIR/count-only"
  done
done

echo "==> Fixtures in fixtures/certificates/<kind>/accept must be accepted"
for f in "$FIXTURES"/*/accept/*.json; do
  expect accept "$f" "${f#"$FIXTURES"/}"
done

echo "==> Fixtures in fixtures/certificates/reject and <kind>/reject must be rejected"
for f in "$FIXTURES"/reject/*.json "$FIXTURES"/*/reject/*.json; do
  expect reject "$f" "${f#"$FIXTURES"/}"
done

echo "==> Forgery, retention, early-stop and CLI contracts"
if ! python3 "$ROOT_DIR/scripts/test_run_certificates.py"; then status=1; fi
if ! python3 -B "$ROOT_DIR/scripts/test_first_crossing_certificates.py"; then status=1; fi

echo "==> Recorded evaluator runs"
if ! python3 "$ROOT_DIR/scripts/test_evaluate.py"; then status=1; fi

exit "$status"
