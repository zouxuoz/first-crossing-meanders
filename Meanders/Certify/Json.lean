import Lean.Data.Json
import Meanders.Certify.Count

/-! Parse the common numerical claim fields of a versioned run manifest.
Only the run parser accepts an on-disk certificate kind. -/

namespace Meanders.Certify

open Lean (Json)

/-- The fields of a count certificate. -/
def CountCertificate.ofJson? (j : Json) : Except String CountCertificate := do
  let problemTag ← j.getObjValAs? String "problem"
  let some problem := Problem.ofTag? problemTag | throw s!"unknown problem tag: {problemTag}"
  let algorithmTag ← j.getObjValAs? String "algorithm"
  let some algorithm := Algorithm.ofTag? algorithmTag
    | throw s!"unknown algorithm tag: {algorithmTag}"
  let n ← j.getObjValAs? Nat "n"
  let count ← j.getObjValAs? Nat "count"
  pure { problem, algorithm, n, count }

end Meanders.Certify
