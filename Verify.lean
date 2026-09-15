import Meanders.Certify.Verifier
import Meanders.Certify.RunFiles

/-!
`lake exe verify <run.json>` checks full/compact runs with the proved count or
layer checker and reports the actual exact verification route. Other file
kinds are rejected during parsing. IO and reporting remain outside the proof.
-/

open Meanders.Certify

/-- Read and verify the certificate path supplied on the command line. -/
def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: verify <certificate.json>"
      return 1
  let report : Except String Claim → IO UInt32 := fun r => do
    match r with
    | .ok claim =>
      IO.println s!"ACCEPT: {claim.problem.tag} meander number {claim.n} = {claim.count}"
      return 0
    | .error reason =>
      IO.println s!"REJECT: {reason}"
      return 1
  let text ← try IO.FS.readFile path catch e =>
    return ← report (.error s!"cannot read certificate {path}: {e}")
  match Lean.Json.parse text >>= parseJson with
  | .error reason => report (.error reason)
  | .ok m =>
    let dir := (System.FilePath.mk path).parent.getD "."
    match ← verifyRunFile dir m with
    | .error e => report (.error e)
    | .ok claim =>
      IO.println (s!"ACCEPT: {claim.problem.tag} meander number {claim.n} = {claim.count} " ++
        s!"({m.verificationMode})")
      return 0
