#!/usr/bin/env bash
# Repository policy checks, run in CI alongside the build.
#
# The axiom audit in `lean-action` already catches `sorry` and `native_decide`
# in theorem dependencies. These checks are stricter and
# cheaper: they catch the same things anywhere in the source, plus the two
# habits that make a Lean project hard to keep honest — a blanket
# `import Mathlib` (which hides what a file needs) and hand-added axioms.
#
# `native_decide` trusts the Lean compiler, so it is banned outside the
# `MeandersTests` library, which is a deliberate escape hatch: nothing there is
# depended on by a theorem. Today it is unused even there.
set -uo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

# Every Lean file we own, ignoring dependencies and build output.
# (Written as a read loop rather than `mapfile`: bash 3.2 still ships on macOS.)
LEAN_FILES=()
while IFS= read -r f; do LEAN_FILES+=("$f"); done < <(git ls-files '*.lean')
NON_TEST_FILES=()
for f in "${LEAN_FILES[@]}"; do
  case "$f" in MeandersTests.lean|MeandersTests/*) ;; *) NON_TEST_FILES+=("$f") ;; esac
done

if [[ ${#LEAN_FILES[@]} -eq 0 ]]; then
  echo "FAIL: no Lean files found; is this a git checkout?" >&2
  exit 1
fi

status=0

check() { # check <label> <grep-extended-regex> <file...>
  local label=$1 pattern=$2
  shift 2
  local hits
  hits=$(grep -nE "$pattern" "$@" 2>/dev/null || true)
  if [[ -n $hits ]]; then
    echo "    FAIL: $label" >&2
    printf '%s\n' "$hits" >&2
    status=1
  else
    echo "    ok: $label"
  fi
}

echo "==> Lean source policy"
# `\b` is not portable across greps; anchor on the token boundaries we care about.
check "no sorry"                '(^|[^[:alnum:]_.])sorry([^[:alnum:]_]|$)' "${LEAN_FILES[@]}"
check "no admit"                '(^|[^[:alnum:]_.])admit([^[:alnum:]_]|$)' "${LEAN_FILES[@]}"
check "no new axioms"           '^[[:space:]]*axiom[[:space:]]' "${LEAN_FILES[@]}"
check "no bare import Mathlib"  '^import Mathlib$' "${LEAN_FILES[@]}"
check "no native_decide outside MeandersTests" \
  '(^|[^[:alnum:]_.])native_decide([^[:alnum:]_]|$)' "${NON_TEST_FILES[@]}"

echo "==> Lean layer rules (ARCHITECTURE.md)"
if ! python3 "$ROOT_DIR/scripts/test_check_imports.py"; then
  status=1
fi
if python3 "$ROOT_DIR/scripts/check_imports.py"; then
  echo "    ok: every import respects the layer table"
else
  echo "    FAIL: import rule violated (see above)" >&2
  status=1
fi

echo "==> Known values agree between Lean and fixtures/oeis/"
# One file per problem, fixtures/oeis/<tag>.txt, against the Lean list
# <tag>MeanderNumbers in KnownValues.lean; both directions must exist.
if python3 - "$ROOT_DIR" <<'PY'
import glob, os, re, sys
root = sys.argv[1]
lean = open(f"{root}/Meanders/Verification/KnownValues.lean", encoding="utf-8").read()
lean_tables = {
    name: [(int(a), int(b)) for a, b in re.findall(r"\((\d+),\s*(\d+)\)", body)]
    for name, body in re.findall(r"def (\w+)MeanderNumbers : List \(Nat × Nat\) :=\s*\[(.*?)\]", lean, re.S)
}
files = {os.path.basename(f)[:-4]: f for f in glob.glob(f"{root}/fixtures/oeis/*.txt")}
ok = True
for tag in sorted(set(lean_tables) | set(files)):
    if tag not in files:
        print(f"    Lean table {tag}MeanderNumbers has no fixtures/oeis/{tag}.txt", file=sys.stderr); ok = False; continue
    if tag not in lean_tables:
        print(f"    fixtures/oeis/{tag}.txt has no Lean table {tag}MeanderNumbers", file=sys.stderr); ok = False; continue
    data = []
    for line in open(files[tag], encoding="utf-8"):
        line = line.strip()
        if line and not line.startswith("#"):
            n, c = line.split()
            data.append((int(n), int(c)))
    if data != lean_tables[tag]:
        print(f"    {tag}: Lean {lean_tables[tag]}\n    {tag}: data {data}", file=sys.stderr); ok = False
sys.exit(0 if ok else 1)
PY
then
  echo "    ok: every Lean table matches its fixtures/oeis/<problem>.txt"
else
  echo "    FAIL: known values differ" >&2
  status=1
fi

exit "$status"
