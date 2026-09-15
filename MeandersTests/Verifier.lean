import Meanders.Certify.Verifier

/-!
# Accept and reject paths of the verifier

Orders are kept small: the count checker recomputes, so each accepting
`#guard` costs a full brute-force run. The certificate fixtures in
`fixtures/certificates/` cover the same paths end to end through the executable.
-/

-- This executable test module intentionally uses `#guard` assertions.
set_option linter.hashCommand false

namespace MeandersTests

open Meanders.Certify

-- Exercise the retained mathematical count checker independently of the wire format.
private def checkCount (s : String) : Except String Claim := do
  let c ← (Lean.Json.parse s >>= CountCertificate.ofJson?).mapError
    (s!"malformed certificate: {·}")
  c.claim?

private def accepts (s : String) : Bool :=
  checkCount s matches .ok _

private def rejectsWith (s reason : String) : Bool :=
  match checkCount s with
  | .error r => r == reason
  | .ok _ => false

private def countCert (problem algorithm n count : String) : String :=
  "{\"problem\":\"" ++ problem ++
    "\",\"algorithm\":\"" ++ algorithm ++ "\",\"n\":" ++ n ++
    ",\"count\":" ++ count ++ "}"

#guard accepts (countCert "closed" "first_crossing" "0" "0")
#guard accepts (countCert "open" "first_crossing" "0" "1")
#guard accepts (countCert "closed" "first_crossing" "3" "8")
#guard accepts (countCert "open" "first_crossing" "5" "8")
#guard accepts (countCert "open" "first_crossing" "6" "14")
#guard rejectsWith (countCert "open" "first_crossing" "6" "28")
  "claimed count does not match the proved counter"
#guard rejectsWith (countCert "closed" "unknown" "1" "1")
  "malformed certificate: unknown algorithm tag: unknown"
#guard accepts (countCert "closed" "first_crossing_optimized" "0" "0")
#guard accepts (countCert "open" "first_crossing_optimized" "0" "1")
#guard accepts (countCert "closed" "first_crossing_optimized" "3" "8")
#guard accepts (countCert "open" "first_crossing_optimized" "5" "8")
#guard accepts (countCert "open" "first_crossing_optimized" "6" "14")
#guard rejectsWith (countCert "open" "first_crossing_optimized" "6" "28")
  "claimed count does not match the proved counter"

private def closedCount (n count : String) : String :=
  countCert "closed" "brute_force" n count

#guard accepts (closedCount "0" "0")
#guard accepts (closedCount "1" "1")
#guard accepts (closedCount "4" "42")
#guard checkCount (closedCount "4" "42") == .ok { problem := .closed, n := 4, count := 42 }
#guard rejectsWith (closedCount "4" "41") "claimed count does not match the proved counter"
#guard rejectsWith (closedCount "1" "0") "claimed count does not match the proved counter"
#guard rejectsWith (countCert "unknown" "brute_force" "4" "8")
  "malformed certificate: unknown problem tag: unknown"
/-! A count beyond 64 bits is parsed as a `Nat` and judged on its merits, not
rejected as malformed: the schema has no integer width. -/
#guard rejectsWith (closedCount "1" "340282366920938463463374607431768211455")
  "claimed count does not match the proved counter"
#guard
  (checkCount "{\"problem\":\"closed\",\"algorithm\":\"brute_force\",\"n\":4}")
    matches .error _
#guard
  (checkCount "{\"algorithm\":\"brute_force\",\"n\":4,\"count\":42}")
    matches .error _
#guard (checkCount "not json") matches .error _

-- Only run files enter the JSON verifier; other kinds fail before other fields.
#guard verifyString (include_str ".."/"fixtures"/"certificates"/"reject"/
  "unknown-certificate-kind.json") == .error "unrecognized certificate kind: tree"
#guard verifyString (include_str ".."/"fixtures"/"certificates"/"run"/"accept"/
  "closed-brute_force-3-compact.json") == .ok ⟨.closed, 3, 8⟩

-- Lean's object parser keeps the last duplicate field; Rust rejects these inputs.
private def checkDuplicateFields : Except String Unit := do
  let json ← Lean.Json.parse (include_str ".."/"fixtures"/"certificates"/"json-duplicates.json")
  let cases ← json.getArr?
  if cases.isEmpty then throw "no duplicate-field cases"
  for c in cases do
    let text ← c.getObjValAs? String "text"
    let claim ← verifyString text
    if claim != ⟨.open, 0, 1⟩ then throw "unexpected duplicate-field interpretation"

#guard checkDuplicateFields == .ok ()

end MeandersTests
