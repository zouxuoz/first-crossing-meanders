# Certificate format and fixtures

Version one uses `kind: "run"`. Problems are `closed` and `open`; algorithms are
`brute_force`, `first_crossing`, and `first_crossing_optimized`. Other tags reject.
`n` is the closed order or open crossing count. Claims and weights are exact JSON
integers; consumers must avoid floating-point conversion. Rust rejects negative,
string, fractional, and exponent-form claims.

## Manifests and retention

See [a count manifest](first-crossing/closed-3-count.json) and
[a sector manifest](first-crossing/closed-2-full.json) for complete examples.

- `representation: "count"`: compact, no layers or First-Crossing metadata;
  verification recomputes the registered count. Selected by `--cert count`,
  and used for all brute-force runs.
- `representation: "first-crossing-lower-jet"`: sector layers plus `firstCrossing`
  metadata binding native order, threshold, both joint outputs, and ordered sectors.
- `profile: "full"`: every descriptor names a canonical layer file.
- `profile: "compact"`: omitted files are regenerated; optional retained files
  are checked. Paths resolve against the manifest directory or may be absolute.
  Missing, unreadable, or invalid referenced files reject.

`--cert auto` selects full through public index 8, compact above it.
`--problem all` uses the native index and writes Closed(n), Open(2n), and
Open(2n-1) manifests sharing layers; the zero case emits Closed(0) and Open(0).
Full and compact versions of the same run have identical roots. Producer tags
are committed, so equivalent reference and optimized runs have different roots.

## Canonical layers

Rows use numeric native-key order, canonical natural decimals, and LF endings:

```text
cpl,cpr,cql,cqr|mate0,mate1,... C E
```

The mate field may be empty. `C` is ordinary weight; `E` is unbonused lower-return
weight. At native order m, each sector contains its seed and all `2m` successor
layers, including empty layers. All four transition labels count even when targets coincide.
A HIGH sector with positive lower cut height adds its ordinary terminal weight
once as `bonusContribution`; summaries keep this separate from `lowerReturns`.
Every lower-jet descriptor requires `lowerReturns` and `symmetric: null`.
The nullable `symmetric` slot retains its checked u128 parser and commitment position.

## Commitments

Each descriptor's `sha256` hashes canonical layer bytes. The root uses the
[RFC 9162](https://www.rfc-editor.org/rfc/rfc9162.html#section-2.1) construction:
`SHA256(0x00 || leaf)` and `SHA256(0x01 || left_digest || right_digest)` with raw
32-byte child digests. Split at the largest power of two below the leaf count;
do not duplicate the last leaf. Digests use lowercase hexadecimal.

The first leaf is this ASCII header, with LF after every line, including the last:

```text
meanders-run-v1
<problem tag>
<algorithm tag>
<n>
<count>
<representation>
<number of layers>
```

Sector manifests append the following bytes (`\n` denotes LF), with one summary
block per sector in native enumeration order:

```text
first-crossing\n{nativeOrder}\n{threshold}\n{closed}\n{openEven}\n{sectorCount}\n
sector\nlow\n{ordinary}\n{lowerReturns}\n{bonusContribution}\n
sector\nhigh\n{cut}\n{upper}\n{lower}\n{ordinary}\n{lowerReturns}\n{bonusContribution}\n
```

The remaining leaves are descriptors in array order, also ASCII with final LF:

```text
layer
<zero-based index>
<rows>
<bytes>
<ordinary mass>
<symmetric mass, or ->
<lowercase sha256>
```

Lower-jet descriptors append `lower-returns\n{lowerReturns}\n` after the SHA line.
Count headers have no sector extension. Numbers are unsigned decimal without
leading zeros, except zero itself. JSON formatting, profiles, and paths are
outside the commitment. See [architecture](../../ARCHITECTURE.md#proof-boundaries)
for numerical verification and kernel replay boundaries.

## Fixtures

- `run/accept/`: Rust parses the claim and Lean accepts it.
- `run/reject/`: Lean rejects invalid metadata, commitments, layers, or counts.
  Rust may parse a false count; it does not numerically verify claims.
- `reject/`: malformed JSON and unknown/missing kinds or incompatible representations.
- `first-crossing/`: full/compact order-two runs, Open(2)'s positive HIGH bonus,
  zero metadata (K=0, no sectors/layers, joint outputs (0,1)), and a count-only root.
- `json-duplicates.json`: Rust rejects duplicate recognized fields; Lean keeps
  the last value. `sha256-vectors.json` supplies shared hash vectors.

Regenerate a sector fixture from the repository root, choosing its problem,
index, and retention profile:

```sh
cargo run --manifest-path rust/Cargo.toml -- count --algorithm first_crossing \
  --problem closed --n 2 --cert full \
  --out fixtures/certificates/first-crossing/closed-2-full.json
```

`./scripts/pipeline.sh` reruns the Lean JSON corpora and both certificate test
scripts. They cover commitments, full/compact/mixed retention, early stopping,
unknown tags, and coherent forgeries. The CLI contract is exit 0 with one
`ACCEPT` report or exit 1 with one `REJECT` report, without stderr.
First-Crossing tests default to native order three; use
`python3 scripts/test_first_crossing_certificates.py --max-order 8` for wider coverage.
`scripts/replay.sh` separately tests numerical kernel replay and false claims.
