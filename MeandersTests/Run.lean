import Meanders.Certify.Run

/-! Shared SHA-256 and RFC 9162 vectors, computed independently using Python's
hashlib; cover padding boundaries, multiblock UTF-8 and non-power-of-two trees. -/
set_option linter.hashCommand false

namespace MeandersTests

private def checkHashVectors : Except String Unit := do
  let json ← Lean.Json.parse (include_str ".."/"fixtures"/"certificates"/"sha256-vectors.json")
  for v in ← json.getObjValAs? (Array Lean.Json) "sha256" do
    let text ← v.getObjValAs? String "text"
    let expected ← v.getObjValAs? String "sha256"
    if Meanders.Certify.Sha256.hash text.toUTF8 != expected then
      throw s!"SHA-256 vector mismatch at {text.length} characters"
  for v in ← json.getObjValAs? (Array Lean.Json) "merkle" do
    let leaves ← v.getObjValAs? (Array String) "leaves"
    let expected ← v.getObjValAs? String "root"
    if Meanders.Certify.Sha256.hex (Meanders.Certify.Sha256.merkle
        (leaves.toList.map String.toUTF8)) != expected then
      throw s!"Merkle vector mismatch at {leaves.size} leaves"

#guard checkHashVectors == .ok ()

end MeandersTests
