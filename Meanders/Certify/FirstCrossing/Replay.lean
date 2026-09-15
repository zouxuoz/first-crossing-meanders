import Meanders.Certify.FirstCrossing.Correct
import Meanders.Certify.FirstCrossing.CountReplay

/-! Native reference replay candidates; constructing data is not numerical acceptance. -/
namespace Meanders.Certify

namespace FirstCrossingRun

/-- Convert the cursor horizon to the same fixed stage for reducible successor replay. -/
def replayNext (spec : FirstCrossing.RunSpec) (remaining : ℕ)
    (rows : FirstCrossing.Layer) : FirstCrossing.Layer :=
  replayNextLayer spec (FirstCrossing.Stage.ofTick spec (2 * spec.n - remaining)) rows

/-- The replay cursor compares exactly the original native successor. -/
theorem replayNext_eq (spec : FirstCrossing.RunSpec) :
    replayNext spec = FirstCrossingSectorTable.next spec := by
  funext remaining rows
  exact replayNextLayer_eq _ _ _

/-- Reuse the shared loaded cursor and terminal finisher with the proved reducible successor. -/
def replaySectorCheck (spec : FirstCrossing.RunSpec) (layers : List FirstCrossing.Layer)
    (claimed : FirstCrossingSectorTable.Summary) :
    Except String FirstCrossingSectorTable.Summary := do
  let first :: rest := layers | throw "no First-Crossing layers"
  let cursor ← if spec.valid then
    LayerStream.start (replayNext spec) FirstCrossingSectorTable.initial (2 * spec.n) first
    else .error "invalid First-Crossing sector metadata"
  cursor.checkRemaining rest (fun cursor =>
    FirstCrossingSectorTable.finishLayer spec cursor.remaining cursor.layer claimed)

/-- Reducible replay changes neither acceptance nor any returned summary. -/
theorem replaySectorCheck_eq : replaySectorCheck = FirstCrossingSectorTable.check := by
  funext spec layers claimed
  unfold replaySectorCheck FirstCrossingSectorTable.check
  rw [replayNext_eq]
  cases layers with
  | nil => rfl
  | cons first rest =>
    by_cases hv : spec.valid = true <;>
      simp [hv, FirstCrossingSectorTable.start, FirstCrossingSectorTable.finish]

/-- Replay the same ordered certificate, with no second parser or semantic recurrence. -/
def Certificate.replayClaim? (c : Certificate) : Except String Claim :=
  c.claimWith replaySectorCheck

/-- Exact equality to the public certificate checker. -/
theorem Certificate.replayClaim?_eq (c : Certificate) : c.replayClaim? = c.claim? := by
  unfold Certificate.replayClaim?
  rw [replaySectorCheck_eq]

/-- Kernel checking the reducible replay proves the original public numerical claim. -/
theorem Certificate.replayClaim?_sound {c : Certificate} {claim : Claim}
    (h : c.replayClaim? = .ok claim) : claim.Correct :=
  Certificate.claim?_sound ((Certificate.replayClaim?_eq c).symm.trans h)

end FirstCrossingRun

/-- Generate explicit canonical rows for every physical tick using the actual successor. -/
def FirstCrossingRun.sectorReplayLayers (spec : FirstCrossing.RunSpec) :
    List FirstCrossing.Layer :=
  (List.range (2 * spec.n)).scanl (fun rows tick =>
    FirstCrossing.nextLayer spec (FirstCrossing.Stage.ofTick spec tick) rows)
    FirstCrossingSectorTable.initial

/-- A proof candidate carries explicit layers; incorrect advertised summaries still fail replay. -/
def FirstCrossingRun.replayCertificate (claim : Claim) (metadata : FirstCrossingRun.Metadata) :
    FirstCrossingRun.Certificate :=
  ⟨claim, metadata, if metadata.nativeOrder = 0 then [] else
    (FirstCrossing.sectorSpecs metadata.nativeOrder metadata.threshold).flatMap
      FirstCrossingRun.sectorReplayLayers⟩

end Meanders.Certify
