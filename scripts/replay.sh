#!/usr/bin/env bash
# Export concrete counts and require kernel replay, including failure paths.
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"
WORK_DIR="$(mktemp -d)"
trap 'rm -rf "$WORK_DIR"' EXIT

cargo build --release --manifest-path rust/Cargo.toml
lake --wfail build exportTheorem Meanders.Certify

replay() { # problem algorithm index source-name; compare checked-in artifacts when present
  local problem=$1 algorithm=$2 n=$3 name=$4 profile=${5:-compact}
  rust/target/release/meanders count --problem "$problem" --algorithm "$algorithm" \
    --n "$n" --cert "$profile" --out "$WORK_DIR/count.json"
  .lake/build/bin/exportTheorem "$WORK_DIR/count.json" "$WORK_DIR/$name.lean"
  if [[ -f "Meanders/Certify/Examples/$name.lean" ]]; then
    diff -u "Meanders/Certify/Examples/$name.lean" "$WORK_DIR/$name.lean"
  fi
  lake env lean "$WORK_DIR/$name.lean"
}

# Shared First-Crossing outputs, positive HIGH bonus, parity and both zeros.
replay closed first_crossing 2 FirstCrossingClosed2
replay open first_crossing 2 FirstCrossingOpen2
replay open first_crossing 3 FirstCrossingOpen3
replay open first_crossing 4 FirstCrossingOpen4 full
replay closed first_crossing 0 FirstCrossingClosedZero
replay open first_crossing 0 FirstCrossingOpenZero
# Packed producer tags reuse the same exact sector and count-only replay proof.
replay closed first_crossing_optimized 2 FirstCrossingOptimizedClosed2
replay open first_crossing_optimized 4 FirstCrossingOptimizedOpen4 full
replay open first_crossing_optimized 0 FirstCrossingOptimizedOpenZero
# Compatible count runs use the independent count replay route. Exercise true
# claims as well as the false claims below; new producers prefer sector evidence.
for algorithm in first_crossing first_crossing_optimized; do
  for example in closed:2 open:3 open:4 closed:0 open:0; do
    IFS=: read -r problem n <<< "$example"
    rust/target/release/meanders count --problem "$problem" --algorithm "$algorithm" \
      --n "$n" --cert count --out "$WORK_DIR/count-only.json"
    .lake/build/bin/exportTheorem "$WORK_DIR/count-only.json" "$WORK_DIR/CountOnly.lean"
    grep -F 'CountCertificate.correct_of_firstCrossingCount' "$WORK_DIR/CountOnly.lean" >/dev/null
    lake env lean "$WORK_DIR/CountOnly.lean"
  done
done

reject_false_proof() { # proof path, diagnostic label
  local proof=$1 label=$2 code
  if lake env lean "$proof" > "$WORK_DIR/false.log" 2>&1; then
    echo "FAIL: false $label numerical theorem replayed" >&2
    exit 1
  else
    code=$?
  fi
  if [[ $code -ne 1 ]] || ! grep -F 'Tactic `decide` proved that the proposition' "$WORK_DIR/false.log" >/dev/null \
    || ! grep -Fx 'is false' "$WORK_DIR/false.log" >/dev/null; then
    cat "$WORK_DIR/false.log" >&2
    echo "FAIL: expected a false-proposition diagnostic, not an execution error" >&2
    exit 1
  fi
}

# False data can be exported; only kernel rejection establishes the negative test.
for example in closed:1:0:first_crossing open:2:0:first_crossing open:0:0:first_crossing closed:1:0:first_crossing_optimized open:2:0:first_crossing_optimized; do
  IFS=: read -r problem n count algorithm <<< "$example"
  rust/target/release/meanders count --problem "$problem" --algorithm "$algorithm" \
    --n "$n" --cert compact --out "$WORK_DIR/false.json"
  PYTHONPATH="$ROOT_DIR/scripts${PYTHONPATH:+:$PYTHONPATH}" python3 - "$WORK_DIR/false.json" "$count" <<'PYTEST'
import json, pathlib, sys
from test_run_certificates import commitment
path = pathlib.Path(sys.argv[1])
m = json.loads(path.read_text())
m['count'] = int(sys.argv[2])
# A false count-only claim reaches numerical kernel replay independently of
# lower-jet metadata consistency and retained payload validation.
if m['algorithm'] in ('first_crossing', 'first_crossing_optimized'):
    m.update(representation='count', layers=[])
    m.pop('firstCrossing')
m['root'] = commitment(m)
path.write_text(json.dumps(m))
PYTEST
  .lake/build/bin/exportTheorem "$WORK_DIR/false.json" "$WORK_DIR/False.lean"
  reject_false_proof "$WORK_DIR/False.lean" "$problem"
done

# Export regenerates canonical layers and rejects the doubled summaries during
# kernel replay. Retained-payload seed rejection is tested by the file verifier
# in test_first_crossing_certificates.py, not by this exporter.
rust/target/release/meanders count --problem open --algorithm first_crossing \
  --n 2 --cert full --out "$WORK_DIR/false-lower-jet.json"
PYTHONPATH="$ROOT_DIR/scripts${PYTHONPATH:+:$PYTHONPATH}" python3 -B - "$WORK_DIR/false-lower-jet.json" <<'PYTEST'
import json, pathlib, sys
from test_first_crossing_certificates import scale_weights
from test_run_certificates import commitment
path = pathlib.Path(sys.argv[1])
m = json.loads(path.read_text())
scale_weights(m, path.parent, 'scaled-false')
m['root'] = commitment(m)
path.write_text(json.dumps(m))
PYTEST
.lake/build/bin/exportTheorem "$WORK_DIR/false-lower-jet.json" "$WORK_DIR/FalseLowerJet.lean"
reject_false_proof "$WORK_DIR/FalseLowerJet.lean" "First-Crossing lower-jet"

for fixture in reject/unknown-certificate-kind.json run/reject/claim-unknown-algorithm.json reject/not-json.json; do
  if .lake/build/bin/exportTheorem "fixtures/certificates/$fixture" "$WORK_DIR/Unsupported.lean"; then
    echo "FAIL: exported unsupported or malformed input $fixture" >&2
    exit 1
  else
    code=$?
    if [[ $code -ne 1 ]]; then
      echo "FAIL: exporter exited abnormally ($code)" >&2
      exit 1
    fi
  fi
done
test ! -e "$WORK_DIR/Unsupported.lean"
echo "ok: canonical exports, kernel replay, zero conventions, false claims, and unsupported inputs"
