# First-Crossing meanders

Exact closed and open meander counts, computed in Rust and verified in Lean.
Lean proves the shared First-Crossing evaluator correct and bounds each layer
by `O*(2^n)` keys at closed order n. The [preprint](blueprint/src/print.tex)
explains the construction and argues the polynomial-factor time and space bound.

## Build and count

Install elan and rustup; the repository pins both toolchains. From its root:

```sh
lake exe cache get
lake build
cargo build --release --manifest-path rust/Cargo.toml

CERT_DIR="$(mktemp -d)"
rust/target/release/meanders count --problem open --algorithm first_crossing \
  --n 6 --cert compact --out "$CERT_DIR/open.json"
lake exe verify "$CERT_DIR/open.json"
# ACCEPT: open meander number 6 = 14 (exact layer recomputation)
```

`--n` is the order for closed meanders (2n crossings) and the crossing count
for open meanders. Closed(0)=0; Open(0)=1. Both problems support:

- `brute_force`: the independent small-order oracle and CLI default.
- `first_crossing`: the readable reference engine.
- `first_crossing_optimized`: the packed engine; `--threads 4` enables bounded
  parallelism (one worker by default; requests above 256, one worker per
  key-hash bucket, use 256).

The default problem is `closed`. `--cert full` retains layers; `--cert compact`
regenerates them during verification; `--cert count` recomputes only the count.
`--problem all --n 3 --out <directory>` emits Closed(3)=8, Open(6)=14 and
Open(5)=8 from one First-Crossing run; select either First-Crossing algorithm.

## Record a native run

After building, record certificates, timings, peak RSS and compiled Lean verdicts:

```sh
lake build verify
python3 scripts/evaluate.py --host m2max \
  --evaluator first_crossing_optimized --n 3
```

The harness accepts `first_crossing` and `first_crossing_optimized`, always using
`--problem all`: native order n gives Closed(n), Open(2n) and Open(2n-1) where
supported. `--threads 4` enables optimized workers; the default is one.
`--cert auto` follows the CLI policy; `full`, `compact` and `count` override it.
`--verify auto` checks through native order 10; use `always` or `never` to override.

Each run creates `evaluations/<evaluator>/n-<N>/<UTC timestamp>/` with certificates
and `meta.json`, preserving earlier runs. `--out` changes this gitignored default
root. Metadata records exact counts, certificate roots, binary hashes, revision,
host, commands and separate production/verification measurements. Failed runs
retain reports and exit nonzero; skipped verification is null, and acceptance
requires every emitted certificate to pass. See `scripts/evaluate.py --help`.

## Kernel replay

The verifier's compiled `ACCEPT` output is distinct from a kernel-checked
numerical theorem. To export and replay a small example:

```sh
rust/target/release/meanders count --problem open --algorithm first_crossing \
  --n 4 --cert compact --out "$CERT_DIR/open4.json"
lake exe exportTheorem "$CERT_DIR/open4.json" "$CERT_DIR/Open4.lean"
lake env lean "$CERT_DIR/Open4.lean"
```

Successful replay proves Open(4)=3; export alone creates a proof candidate.

## Project guide

- [Architecture](ARCHITECTURE.md): dependencies, proof boundaries, validation,
  and preprint PDF/web build commands.
- [Contributor instructions](AGENTS.md): rules for changes.
- [Certificate format](fixtures/certificates/README.md): version-one bytes and fixtures.
- [Lean specifications](Meanders/Problems) and [First-Crossing proofs](Meanders/Models/FirstCrossing).
