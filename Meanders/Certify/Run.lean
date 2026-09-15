import Meanders.Certify.FirstCrossing.Metadata
import Meanders.Certify.Sha256

/-! One run format, with full or compact retention. Commitments cover canonical
metadata and ordered layer descriptors, independently of file locations/profile.
Numerical acceptance still requires the existing exact count or layer checker. -/

namespace Meanders.Certify

/-- How much layer evidence is retained locally. -/
inductive Profile
  /-- Every layer has a file. -/
  | full
  /-- Layers can be omitted and regenerated during exact verification. -/
  | compact
  deriving Repr, DecidableEq

/-- Per-layer summaries and a SHA-256 commitment to canonical row bytes. -/
structure RunLayer where
  /-- Number of states. -/
  rows : Nat
  /-- Canonical payload byte length. -/
  bytes : Nat
  /-- Sum of ordinary weights. -/
  ordinary : Nat
  /-- Historical channel kept in the wire format and commitment; always `none`. -/
  symmetric : Option Nat
  /-- Lowercase SHA-256 digest. -/
  sha256 : String
  /-- Optional manifest-relative file; excluded from the commitment. -/
  file : Option String
  /-- Original lower-return weight, exclusively for First-Crossing. -/
  lowerReturns : Option Nat := none
  deriving Repr, DecidableEq

/-- The version-one manifest shared by both retention profiles. -/
structure RunManifest where
  /-- The numerical claim and producing evaluator. -/
  claim : CountCertificate
  /-- Retained evidence profile. -/
  profile : Profile
  /-- Versioned row and transition semantics, or count for non-layered evaluators. -/
  representation : String
  /-- Ordered summaries, including the initial and terminal layers. -/
  layers : List RunLayer
  /-- Merkle root of the header followed by the layer descriptors. -/
  root : String
  /-- Ordered native sectors and joint channels, only for First-Crossing layer runs. -/
  firstCrossing : Option FirstCrossingRun.Metadata := none
  deriving Repr, DecidableEq

/-- Canonical semantic header, excluding transport details. -/
def RunManifest.header (m : RunManifest) : String :=
  s!"meanders-run-v1\n{m.claim.problem.tag}\n{m.claim.algorithm.tag}\n{m.claim.n}\n" ++
    s!"{m.claim.count}\n{m.representation}\n{m.layers.length}\n" ++
    (m.firstCrossing.map FirstCrossingRun.Metadata.header).getD ""

/-- Canonical layer descriptor, with its position explicitly bound. -/
def RunLayer.descriptor (l : RunLayer) (t : Nat) : String :=
  s!"layer\n{t}\n{l.rows}\n{l.bytes}\n{l.ordinary}\n" ++
    s!"{l.symmetric.map toString |>.getD "-"}\n{l.sha256}\n" ++
    (l.lowerReturns.map (fun value => s!"lower-returns\n{value}\n")).getD ""

/-- Recompute the metadata commitment. This does not check the numerical claim. -/
def RunManifest.commitment (m : RunManifest) : String :=
  Sha256.hex (Sha256.merkle (m.header.toUTF8 ::
    (m.layers.zipIdx.map fun (l, t) => (l.descriptor t).toUTF8)))

/-- Exactly the existing supported layer representations. -/
def runRepresentation (_p : Problem) (a : Algorithm) : String :=
  if a.isFirstCrossing then FirstCrossingRun.representation
  else "count"

/-- Preferred producer representation plus compatible compact First-Crossing count evidence. -/
def runRepresentationCompatible (p : Problem) (a : Algorithm) (representation : String) : Bool :=
  representation == runRepresentation p a ||
    (a.isFirstCrossing && representation == "count")

/-- Validate tags, layer shape, channels and metadata commitment. -/
def RunManifest.validate (m : RunManifest) : Except String Unit := do
  if !runRepresentationCompatible m.claim.problem m.claim.algorithm m.representation then
    throw "incompatible run representation"
  if m.representation = FirstCrossingRun.representation then
    let some fc := m.firstCrossing | throw "missing First-Crossing metadata"
    fc.validateClaim m.claim.claim
    fc.validateLayerCount m.layers.length
    fc.validate
  else if m.firstCrossing.isSome then
    throw "First-Crossing extension on incompatible representation"
  if m.representation = "count" then
    if m.profile != .compact || !m.layers.isEmpty then
      throw "count requires compact profile and no layers"
  let hex (s : String) := s.length == 64 &&
    s.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))
  for l in m.layers do
    if !hex l.sha256 then throw "invalid SHA-256 digest"
    if l.symmetric.isSome ||
        l.lowerReturns.isSome != (m.representation == FirstCrossingRun.representation) then
      throw "incompatible layer channels"
    if l.file == some "" || (m.profile == .full && l.file.isNone) then
      throw "full profile requires every layer file"
  if !hex m.root || m.root != m.commitment then throw "run root mismatch"

private def optionalField {α : Type} [Lean.FromJson α] (j : Lean.Json) (key : String) :
    Except String (Option α) :=
  match j.getObjVal? key with
  | .error _ => pure none
  | .ok v => Lean.fromJson? v

/-- Parse one layer descriptor; symmetric is explicitly null for unpaired rows. -/
def RunLayer.ofJson? (j : Lean.Json) : Except String RunLayer := do
  pure {
    rows := ← j.getObjValAs? Nat "rows"
    bytes := ← j.getObjValAs? Nat "bytes"
    ordinary := ← j.getObjValAs? Nat "ordinary"
    symmetric := ← j.getObjValAs? (Option Nat) "symmetric"
    sha256 := ← j.getObjValAs? String "sha256"
    file := ← optionalField j "file"
    lowerReturns := ← optionalField j "lowerReturns" }

/-- Parse and validate version-one metadata without accepting the numerical claim. -/
def RunManifest.ofJson? (j : Lean.Json) : Except String RunManifest := do
  let version ← j.getObjValAs? Nat "version"
  if version != 1 then throw "unsupported run version"
  let profile ← match ← j.getObjValAs? String "profile" with
    | "full" => pure Profile.full
    | "compact" => pure Profile.compact
    | _ => throw "unknown run profile"
  let firstCrossing ← match j.getObjVal? "firstCrossing" with
    | .error _ => pure none
    | .ok .null => pure none
    | .ok value => pure (some (← FirstCrossingRun.Metadata.ofJson? value))
  let m : RunManifest := {
    claim := ← CountCertificate.ofJson? j, profile,
    representation := ← j.getObjValAs? String "representation",
    layers := ← (← j.getObjValAs? (Array Lean.Json) "layers").toList.mapM RunLayer.ofJson?,
    root := ← j.getObjValAs? String "root", firstCrossing }
  m.validate
  pure m

end Meanders.Certify
