# Architecture

Normative contracts for the implementation. The blueprint owns the mathematical
exposition; [CI](.github/workflows/ci.yml) runs the validation gates below.

## Dependencies

`Meanders/Core` and `Problems` define matching/graph objects and public counts.
`Models/FirstCrossing` follows this dependency order:
`Original` (source partition) → `Native` (carrier and evaluator) → `Surgery`
(totality) → `Interpretation` (source paths) → `Correctness` (public counts).
Each directory imports only itself or earlier directories. `Packed` provides
the bounded oriented codec and its successor correspondence.

| Lean layer | May import project layers |
| --- | --- |
| Core | Core |
| Problems | Core, Problems |
| Models | Core, Problems, Models |
| Algorithms | Core, Problems, Models, its own algorithm subtree |
| Verification | Core, Problems, Verification |
| Certify | All library layers |

`Algorithms` exposes BruteForce and FirstCrossing. `Verification` holds known-value
regressions; `Certify` owns the registry, schema, checkers, replay, and numerical
examples. `Verify.lean` and `ExportTheorem.lean` are executable roots;
`MeandersTests` is the separate test library.

Library files never import tests or layer umbrellas; umbrellas contain only
imports. Executable roots and tests may import library modules. Policy rejects
bare `import Mathlib`, `sorry`, `admit`, custom axioms, and `native_decide` outside
tests. `scripts/policy.sh` enforces source and layer rules.

## Evaluators and compatibility

The public matching boundary is `Fin (2n)`. Problems are closed (order n,
zero count 0) and open (crossing count q, zero count 1). The registry supports
`brute_force`, `first_crossing`, and `first_crossing_optimized` for both;
unknown problem, algorithm, and kind tags reject without aliases.
Brute force and pinned known values provide independent regression checks.

First-Crossing uses original counters and a fully oriented pairing carrier,
with exact ordinary/lower-return weights and one terminal HIGH bonus. There
is no symmetry division or owner quotient. The optimized Rust engine preserves
canonical rows, defaults to one worker (at most 256, one per key-hash
bucket), and falls back to the reference beyond 64 ports or u16 counters. Certificate weights are exact BigUint values.

Both producers use the same proved Lean reference and shared LayerStream sector
cursor. Their `first-crossing-lower-jet` evidence keeps unbonused `lowerReturns`
and `bonusContribution` separate. Count-only evidence remains supported.
Preserve version-one schema and commitment bytes, including the null
`RunLayer.symmetric` slot; see the [byte contract](fixtures/certificates/README.md).

## Proof boundaries

`FirstCrossing.count_eq` proves the evaluator computes the independent public
counts; `evaluateJoint_correct` proves joint Closed/even-Open counts.
`carrierCard_le` bounds per-layer keys. The preprint argues the associated
polynomial-factor time and space bound. The packed codec and decoded successor
list are proved; Rust's direct word surgery is checked differentially.

In `Meanders.Certify`, `verifyString_sound` covers count runs and
`FirstCrossingRun.Certificate.claim?_sound` covers loaded sector evidence.
Verification recomputes counts or exact successor layers; hashes bind bytes.
Compiled execution, runtime, filesystem loading, and reporting are outside the
kernel statements. Layer checking retains consecutive layers plus working storage.

`exportTheorem` emits untrusted proof candidates for First-Crossing sector and
count evidence. Only successful Lean kernel replay proves the concrete equation.
Sector export regenerates canonical evidence rather than validating retained
payloads. Replay is intended for small examples and can be expensive.

## Validation

Run the first three commands sequentially, then the remaining gates. The pipeline
checks Rust/Lean agreement, fixtures, and certificate corruption; replay compares
checked-in proof sources and kernel-checks true and false claims. Lean tests and
the blueprint retain declaration/axiom checks.

```sh
lake build
lake --wfail test
lake lint
./scripts/policy.sh
cargo fmt --check --manifest-path rust/Cargo.toml
cargo clippy --manifest-path rust/Cargo.toml --all-targets -- -D warnings
cargo test --manifest-path rust/Cargo.toml
./scripts/pipeline.sh
./scripts/replay.sh
```

For PDF/web validation, install Python, Graphviz, Poppler, TeX with TikZ, xelatex,
and latexmk. Both targets use `blueprint/src/chapter/` and its bibliography;
build PDF first to supply the web bibliography.

```sh
pip install -r blueprint/requirements.txt
leanblueprint pdf
leanblueprint web
lake exe checkdecls blueprint/lean_decls
python3 scripts/source_links.py --check
python3 scripts/check_blueprint.py
```

Outputs are `blueprint/print/print.pdf` and `blueprint/web/index.html`;
`leanblueprint serve` previews the web build. CI also rejects unresolved print
references/citations and web rendering errors. After changing linked Lean files,
run `python3 scripts/source_links.py` at the commit the links should target.
The [artifact appendix](blueprint/src/chapter/reproduction.tex) identifies the
publication tag and production-run archive. Measure certificate work separately
from count-only runs.

## Parser differences

Rust rejects duplicate recognized JSON fields while Lean keeps the last value;
`json-duplicates.json` pins this behavior. Rust rejects unknown First-Crossing
metadata keys while Lean ignores them; those keys are outside commitment bytes.
