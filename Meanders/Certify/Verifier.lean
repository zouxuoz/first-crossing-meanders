import Meanders.Certify.Run

/-!
# The verifier

`parseJson` accepts versioned run manifests only. `verifyJson` checks count
runs with the proved count checker, and `verifyString_sound` says that every
claim it accepts is true. Layered runs use `verifyRunFile`, which loads
retained or regenerates omitted layers through the proved First-Crossing
cursor; IO and digest checking remain outside the kernel boundary. A root
alone never accepts a count.
-/

namespace Meanders.Certify

open Lean (Json)

/-- Run the count checker and, if it accepts, state the claim. -/
def CountCertificate.claim? (c : CountCertificate) : Except String Claim :=
  if c.check then .ok c.claim
  else .error "claimed count does not match the proved counter"

theorem CountCertificate.claim?_sound {c : CountCertificate} {cl : Claim}
    (h : c.claim? = .ok cl) : cl.Correct := by
  unfold CountCertificate.claim? at h
  split at h
  · cases h; exact c.check_sound ‹_›
  · cases h

/-- Read the sole on-disk kind and its versioned manifest. Other kinds reject
before any claim checking or file loading. -/
def parseJson (j : Json) : Except String RunManifest := do
  let kind ← j.getObjValAs? String "kind"
  if kind != "run" then throw s!"unrecognized certificate kind: {kind}"
  RunManifest.ofJson? j

/-- Verify a count run directly. Layered runs require the file entry point,
which checks retained or regenerated layers and their summaries. -/
def verifyJson (j : Json) : Except String Claim := do
  let m ← parseJson j
  if m.representation = "count" then m.claim.claim?
  else throw "a layered run requires: lake exe verify <manifest.json>"

/-- Parse and verify a certificate encoded as JSON text. -/
def verifyString (s : String) : Except String Claim :=
  Json.parse s >>= verifyJson

/-- Unpacking one step of an `Except` pipeline: the step succeeded, and the
rest succeeded on its result. -/
private theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [Bind.bind, Except.bind]

theorem verifyJson_sound {j : Json} {c : Claim} (h : verifyJson j = .ok c) : c.Correct := by
  unfold verifyJson at h
  obtain ⟨p, -, h⟩ := bind_eq_ok.1 h
  split at h
  · exact CountCertificate.claim?_sound h
  · cases h

theorem verifyString_sound {s : String} {c : Claim} (h : verifyString s = .ok c) : c.Correct := by
  obtain ⟨_, -, h⟩ := bind_eq_ok.1 h
  exact verifyJson_sound h

end Meanders.Certify
