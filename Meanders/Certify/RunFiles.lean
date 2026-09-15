import Meanders.Certify.FirstCrossing.Check
import Meanders.Certify.FirstCrossing.Format
import Meanders.Certify.Verifier

/-! Versioned run verification. Retained layers pass exact successor comparison;
omitted layers are regenerated through the same proved cursor. SHA-256 and
summaries are additional rejection checks, never substitutes for the recurrence. -/

namespace Meanders.Certify

private def checkSummary (r : RunLayer) (text : String) (rows ordinary : Nat)
    (symmetric : Option Nat) (lowerReturns : Option Nat := none) : Except String Unit := do
  if r.rows != rows || r.ordinary != ordinary || r.symmetric != symmetric ||
      r.lowerReturns != lowerReturns then
    throw "layer summary mismatch"
  -- Retained bytes were already hashed by the loader before parsing.
  if r.file.isNone then
    let bytes := text.toUTF8
    if r.bytes != bytes.size then throw "layer byte count mismatch"
    if r.sha256 != Sha256.hash bytes then throw "layer SHA-256 mismatch"

private def loadRunLayer {L : Type} (dir : System.FilePath) (file : String) (r : RunLayer)
    (parse : String → Except String L) (format : L → String) : IO (Except String L) := do
  let path := dir / file
  let bytes ← try IO.FS.readBinFile path catch e =>
    return .error s!"cannot read layer file {path}: {e}"
  if r.bytes != bytes.size || r.sha256 != Sha256.hash bytes then
    return .error s!"layer SHA-256 or byte count mismatch for {file}"
  let some text := String.fromUTF8? bytes | return .error "layer is not valid UTF-8"
  return do
    let layer ← parse text
    if format layer != text then throw "run layers require canonical row bytes"
    pure layer

/-- Check a retained or regenerated layer chain. Explicit file references never
silently fall back to recomputation if reading or checking the file fails. -/
def verifyRunLayers {L R : Type} [DecidableEq L] (dir : System.FilePath) (steps : Nat)
    (initial : L) (next : Nat → L → L) (parse : String → Except String L) (format : L → String)
    (check : RunLayer → L → Except String Unit)
    (finish : LayerStream next initial steps → Except String R)
    (refs : List RunLayer) : IO (Except String R) := ExceptT.run do
  if refs.length != steps + 1 then throw "wrong number of run layers"
  let first :: rest := refs | throw "no run layers"
  let layer ← match first.file with
    | some file => ExceptT.mk (loadRunLayer dir file first parse format)
    | none => pure initial
  let mut cursor ← LayerStream.start next initial steps layer
  check first cursor.layer
  for r in rest do
    cursor ← match r.file with
      | some file => do
        let layer ← ExceptT.mk (loadRunLayer dir file r parse format)
        cursor.push layer
      | none => cursor.advance
    check r cursor.layer
  finish cursor

private def checkFirstCrossing (r : RunLayer) (layer : FirstCrossing.Layer) :
    Except String Unit :=
  checkSummary r (FirstCrossingSectorTable.formatLayer layer) layer.length
    (layer.map fun row => row.2.1).sum none (some (layer.map fun row => row.2.2).sum)

/-- Check every source sector with the existing consecutive-layer cursor. File
failures remain fatal, and omitted payloads use the same exact labelled transition. -/
def verifyFirstCrossingRun (dir : System.FilePath) (metadata : FirstCrossingRun.Metadata)
    (refs : List RunLayer) : IO (Except String FirstCrossing.Counts) := ExceptT.run do
  metadata.validateLayerCount refs.length
  metadata.validate
  if metadata.nativeOrder = 0 then return (0, 1)
  let mut rest := refs
  let mut total : FirstCrossing.Counts := (0, 0)
  for (summary, index) in metadata.sectors.zipIdx do
    let spec : FirstCrossing.RunSpec :=
      ⟨metadata.nativeOrder, metadata.threshold, summary.sector⟩
    let size := 2 * spec.n + 1
    let checked ← ExceptT.mk (do
      let result ← verifyRunLayers dir (2 * spec.n)
        FirstCrossingSectorTable.initial (FirstCrossingSectorTable.next spec)
        FirstCrossingSectorTable.parseLayer FirstCrossingSectorTable.formatLayer checkFirstCrossing
        (fun cursor => FirstCrossingSectorTable.finish cursor summary.toSummary) (rest.take size)
      pure (result.mapError fun e =>
        s!"First-Crossing sector {index} ({repr summary.sector}), " ++
          s!"starting at global layer {index * size}: {e}"))
    total := (total.1 + checked.ordinary, total.2 + checked.openEven)
    rest := rest.drop size
  if !rest.isEmpty then throw "extra First-Crossing layers"
  if total != (metadata.closed, metadata.openEven) then
    throw "First-Crossing checked joint total mismatch"
  return total

/-- Exact numerical verification plus validation of every layer summary and
commitment. A valid root alone cannot produce a numerical acceptance. -/
def verifyRunFile (dir : System.FilePath) (m : RunManifest) : IO (Except String Claim) := do
  match m.validate with
  | .error e => return .error e
  | .ok () => pure ()
  if m.representation == "count" then return m.claim.claim?
  if m.representation == FirstCrossingRun.representation then
    let some metadata := m.firstCrossing | return .error "missing First-Crossing metadata"
    match ← verifyFirstCrossingRun dir metadata m.layers with
    | .error e => return .error e
    | .ok _ => return .ok m.claim.claim
  return .error "incompatible run representation"

/-- Describe the actual numerical verification, independently of the requested profile. -/
def RunManifest.verificationMode (m : RunManifest) : String :=
  if m.representation == "count" then "exact count recomputation"
  else if m.representation == FirstCrossingRun.representation && m.layers.isEmpty then
    "exact zero convention"
  else if m.layers.all (·.file.isSome) then "exact retained-layer checking"
  else if m.layers.all (·.file.isNone) then "exact layer recomputation"
  else "exact retained/regenerated-layer checking"

end Meanders.Certify
