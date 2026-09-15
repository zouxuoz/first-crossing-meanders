import Meanders.Models.FirstCrossing.Correctness.EvalLayer
import Meanders.Certify.LayerStream

/-! Exact First-Crossing sector layers, with local reference-evaluator soundness. -/

namespace Meanders.Certify.FirstCrossingSectorTable

open FirstCrossing

/-- The ordinary empty history carries no original lower return marks. -/
def initial : FirstCrossing.Layer := [(Key.empty, (1, 0))]

/-- Translate the shared cursor's remaining horizon into the fixed physical schedule. -/
def next (spec : RunSpec) (remaining : ℕ) (rows : FirstCrossing.Layer) : FirstCrossing.Layer :=
  nextLayer spec (Stage.ofTick spec (2 * spec.n - remaining)) rows

/-- Existing consecutive-layer cursor specialized to one fixed source sector. -/
abbrev Stream (spec : RunSpec) := LayerStream (next spec) initial (2 * spec.n)

/-- Exact summary channels; the HIGH through contribution is never stored as a
propagated lower-return weight. -/
structure Summary where
  /-- Ordinary terminal multiplicity. -/
  ordinary : ℕ
  /-- Terminal first moment of original lower inward returns, before the bonus. -/
  lowerReturns : ℕ
  /-- Exactly the sector bonus times ordinary terminal multiplicity. -/
  bonusContribution : ℕ
  /-- Lower exterior first moment after applying the single sector bonus. -/
  openEven : ℕ
  deriving DecidableEq, Repr

/-- Read unbonused terminal channels and add the through contribution exactly once. -/
def summarize (spec : RunSpec) (rows : FirstCrossing.Layer) : Summary :=
  let raw := sectorTerminal spec rows
  let bonus := spec.lowerBonus * raw.1
  ⟨raw.1, raw.2, bonus, raw.2 + bonus⟩

/-- Check fixed sector metadata and the exact seed without reordering evidence. -/
def start (spec : RunSpec) (rows : FirstCrossing.Layer) : Except String (Stream spec) :=
  if spec.valid then LayerStream.start (next spec) initial (2 * spec.n) rows
  else .error "invalid First-Crossing sector metadata"

/-- Compare one exact canonical successor using the existing shared cursor. -/
def push {spec : RunSpec} (cursor : Stream spec) (rows : FirstCrossing.Layer) :
    Except String (Stream spec) := cursor.push rows

/-- Regenerate an omitted payload through the same exact reference transition. -/
def advance {spec : RunSpec} (cursor : Stream spec) : Except String (Stream spec) :=
  cursor.advance

private theorem remaining_le {spec : RunSpec} {r : ℕ} {rows : FirstCrossing.Layer}
    (h : CheckedLayers (next spec) (2 * spec.n) initial r rows) : r ≤ 2 * spec.n := by
  induction h with
  | initial => rfl
  | step h ih => omega

/-- Every checked prefix has exactly the same remaining reference computation as
its original seed; this equality uses the actual four-label nextLayer. -/
theorem checked_runLayers {spec : RunSpec} (hv : spec.valid = true)
    {r : ℕ} {rows : FirstCrossing.Layer}
    (h : CheckedLayers (next spec) (2 * spec.n) initial r rows) :
    runLayers spec r (Stage.ofTick spec (2 * spec.n - r)) rows =
      runLayers spec (2 * spec.n) ⟨0, 0, 0⟩ initial := by
  induction h with
  | initial => simp only [Nat.sub_self, Stage.ofTick, List.take_zero, List.count_nil]
  | @step r rows h ih =>
    have hr := remaining_le h
    have hi : 2 * spec.n - (r + 1) < spec.schedule.length := by
      rw [spec.schedule_length hv]
      omega
    let side := spec.schedule[2 * spec.n - (r + 1)]
    have hs : spec.schedule[2 * spec.n - (r + 1)]? = some side :=
      List.getElem?_eq_getElem hi
    have hstage : Stage.ofTick spec (2 * spec.n - r) =
        (Stage.ofTick spec (2 * spec.n - (r + 1))).next side := by
      rw [show 2 * spec.n - r = (2 * spec.n - (r + 1)) + 1 by omega]
      exact Stage.ofTick_next spec _ hs
    change runLayers spec r (Stage.ofTick spec (2 * spec.n - r))
      (nextLayer spec (Stage.ofTick spec (2 * spec.n - (r + 1))) rows) = _
    rw [hstage]
    have hi' := ih
    simp only [runLayers, show (Stage.ofTick spec (2 * spec.n - (r + 1))).tick =
      2 * spec.n - (r + 1) from rfl, hs] at hi'
    exact hi'

/-- At the completed cursor, the retained rows equal the actual reference terminal layer. -/
theorem terminal_layer_eq {spec : RunSpec} (hv : spec.valid = true)
    (cursor : Stream spec) (hr : cursor.remaining = 0) :
    cursor.layer = runLayers spec (2 * spec.n) ⟨0, 0, 0⟩ initial := by
  have h := checked_runLayers hv cursor.checked
  simpa only [hr, runLayers] using h

/-- Finish only at the full horizon, checking every separate summary channel. -/
def finishLayer (spec : RunSpec) (remaining : ℕ) (layer : FirstCrossing.Layer)
    (claimed : Summary) : Except String Summary :=
  if spec.valid then
    if remaining = 0 then
      if claimed = summarize spec layer then .ok claimed
      else .error "First-Crossing terminal summary mismatch"
    else .error s!"missing {remaining} First-Crossing layers"
  else .error "invalid First-Crossing sector metadata"

/-- Finish the checked cursor using its exact remaining horizon and layer. -/
def finish {spec : RunSpec} (cursor : Stream spec) (claimed : Summary) :
    Except String Summary := finishLayer spec cursor.remaining cursor.layer claimed

/-- Accepted summary fields equal the exact reference terminal fields, including
the unbonused lower first moment and its separately stated bonus contribution. -/
theorem finish_summary_sound {spec : RunSpec} {cursor : Stream spec} {claimed result : Summary}
    (h : finish cursor claimed = .ok result) :
    result = summarize spec (runLayers spec (2 * spec.n) ⟨0, 0, 0⟩ initial) := by
  unfold finish finishLayer at h
  split_ifs at h with hv hr hc
  cases h
  rw [hc, terminal_layer_eq hv cursor hr]

/-- The final pair is exactly runSector; no public Problem.number claim is made here. -/
theorem finish_runSector_sound {spec : RunSpec} {cursor : Stream spec} {claimed result : Summary}
    (h : finish cursor claimed = .ok result) :
    (result.ordinary, result.openEven) = runSector spec := by
  have hs := finish_summary_sound h
  have hv : spec.valid = true := by
    unfold finish finishLayer at h
    split at h
    · assumption
    · cases h
  rw [hs]
  simp only [summarize, runSector, hv, initial, ↓reduceIte]

/-- Loaded evidence uses the same start, exact cursor pushes, and terminal check. -/
def check (spec : RunSpec) (layers : List FirstCrossing.Layer) (claimed : Summary) :
    Except String Summary := do
  let first :: rest := layers | throw "no First-Crossing layers"
  let cursor ← start spec first
  cursor.checkRemaining rest (fun cursor => finish cursor claimed)

/-- Successful loaded checks establish the exact local reference-sector result. -/
theorem check_sound {spec : RunSpec} {layers : List FirstCrossing.Layer}
    {claimed result : Summary} (h : check spec layers claimed = .ok result) :
    (result.ordinary, result.openEven) = runSector spec := by
  unfold check at h
  cases layers with
  | nil => cases h
  | cons first rest =>
    change Except.bind (start spec first)
      (fun cursor => cursor.checkRemaining rest (fun cursor => finish cursor claimed)) =
        .ok result at h
    cases hs : start spec first with
    | error e =>
      rw [hs] at h
      change Except.error e = Except.ok result at h
      cases h
    | ok cursor =>
      rw [hs] at h
      change cursor.checkRemaining rest (fun cursor => finish cursor claimed) = .ok result at h
      exact LayerStream.checkRemaining_sound
        (property := fun result : Summary => (result.ordinary, result.openEven) = runSector spec)
        (fun _ _ h => finish_runSector_sound h) h

end Meanders.Certify.FirstCrossingSectorTable
