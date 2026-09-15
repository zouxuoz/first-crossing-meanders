import Meanders.Certify.FirstCrossing.Replay
import Meanders.Certify.Verifier

/-!
`lake exe exportTheorem <run.json> <result.lean>` emits a proof candidate
for a closed or open count. Run `lake env lean result.lean` to check it in the
kernel. Exporting is not acceptance: false counts produce failing proofs.
-/

open Meanders.Certify

/-- Emit explicit certificate data and a kernel-replayed numerical theorem. -/
def theoremSource (c : CountCertificate) : String :=
  "import Meanders.Certify.FirstCrossing.CountReplay\n\n" ++
  "namespace Meanders.Certified\n\n" ++
  "private def certificate : Certify.CountCertificate := {\n" ++
  s!"  problem := {reprStr c.problem}\n  algorithm := {reprStr c.algorithm}\n" ++
  s!"  n := {c.n}\n  count := {c.count}\n" ++ "}\n\n" ++
  "set_option maxRecDepth 10000 in\nset_option maxHeartbeats 1000000 in\n" ++
  "-- Finite move-word enumeration needs a larger local reduction budget.\n" ++
  s!"/-- A concrete {c.problem.tag}-meander count, replayed by the Lean kernel. -/\n" ++
  s!"theorem first_crossing_{c.problem.tag}_n{c.n} : " ++
  s!"{c.problem.tag}MeanderNumber {c.n} = {c.count} :=\n" ++
  "  (Certify.CountCertificate.correct_of_firstCrossingCount certificate\n" ++
  "    (by decide +kernel)).symm\n\nend Meanders.Certified\n"

/-- Emit explicit sector evidence and replay the exact checker in the kernel. -/
def firstCrossingTheoremSource (c : CountCertificate) (metadata : FirstCrossingRun.Metadata) :
    String :=
  let evidence := FirstCrossingRun.replayCertificate c.claim metadata
  "import Meanders.Certify.FirstCrossing.Replay\n\nnamespace Meanders.Certified\n\n" ++
    "private def certificate : Certify.FirstCrossingRun.Certificate :=\n" ++
    reprStr evidence ++ "\n\n" ++
    "set_option maxRecDepth 100000 in\nset_option maxHeartbeats 10000000 in\n" ++
    "-- Explicit sector evidence needs a larger local kernel reduction budget.\n" ++
    s!"/-- A concrete {c.problem.tag} count from exact sector evidence, kernel replayed. -/\n" ++
    s!"theorem first_crossing_{c.problem.tag}_n{c.n} : " ++
    s!"{c.problem.tag}MeanderNumber {c.n} = {c.count} :=\n" ++
    "  (Certify.FirstCrossingRun.Certificate.replayClaim?_sound\n" ++
    "    (c := certificate) (claim := certificate.claim) (by decide +kernel)).symm\n\n" ++
    "end Meanders.Certified\n"

/-- Parse the run schema and write the candidate; replay is a separate command. -/
def main (args : List String) : IO UInt32 := do
  let [input, output] := args
    | IO.eprintln "usage: exportTheorem <run.json> <result.lean>"
      return 1
  let parsed ← try pure (Lean.Json.parse (← IO.FS.readFile input) >>= parseJson) catch e =>
    IO.eprintln s!"cannot read certificate: {e}"
    return 1
  match parsed with
  | .error e => IO.eprintln e; return 1
  | .ok m =>
    let c := m.claim
    if !c.algorithm.isFirstCrossing then
      IO.eprintln "theorem export requires a First-Crossing algorithm"
      return 1
    let source := match m.firstCrossing with
      | some metadata => firstCrossingTheoremSource c metadata
      | none => theoremSource c
    try IO.FS.writeFile output source catch e =>
      IO.eprintln s!"cannot write theorem: {e}"
      return 1
    IO.println s!"Wrote proof candidate to {output}; check it with: lake env lean {output}"
    return 0
