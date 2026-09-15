# Working in this repository

Work only on the requested scope. Keep changes small, clear, and reviewable;
new mathematics and performance work belong in separate PRs.

Read [ARCHITECTURE.md](ARCHITECTURE.md) before changing dependencies or proof
boundaries. It defines the required invariants and validation gates.
The [README](README.md) is the entry point; the blueprint owns mathematical exposition.

Preserve Closed/Open specifications, the First-Crossing recurrence, both Rust
engines, evaluator semantics, and version-one certificate bytes. Preserve public
declaration names and every blueprint `\lean{}` target; explain any statement
simplification in the PR. Tests for unknown tags use the literal `unknown`.

Run `lake build`, `lake --wfail test`, and `lake lint` sequentially, then the
remaining checks in ARCHITECTURE.md. Keep CI on GitHub-hosted Ubuntu runners.
Verify Lean import spelling against exact tracked filenames, even on
case-insensitive systems.
Distinguish compiled certificate acceptance from numerical kernel replay when
reporting validation.

Do not merge PRs or push to `main` without user authorization.
