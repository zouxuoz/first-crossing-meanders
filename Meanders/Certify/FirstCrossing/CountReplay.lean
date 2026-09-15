import Meanders.Certify.Count
import Meanders.Certify.KernelSort

/-! Kernel-reducible sorting for the unchanged native reference recurrence. -/
namespace Meanders.Certify.FirstCrossingRun

open FirstCrossing

/-- The same labelled successor with structurally recursive, provably identical sorting. -/
def replayNextLayer (spec : RunSpec) (stage : Stage) (rows : FirstCrossing.Layer) :
    FirstCrossing.Layer :=
  match KernelSort.sort (rows.flatMap (emitRow spec stage))
      (fun a b => codeLE a.1.sortCode b.1.sortCode) with
  | [] => []
  | row :: rest => mergeRun row rest

/-- Sorting changes reduction behavior only, not any key or weight. -/
theorem replayNextLayer_eq (spec : RunSpec) (stage : Stage) (rows : FirstCrossing.Layer) :
    replayNextLayer spec stage rows = nextLayer spec stage rows := by
  simp only [replayNextLayer, KernelSort.sort_eq, nextLayer, mergeRows]
  rfl

/-- Structural horizon recursion through the same native steps and fixed schedule. -/
def replayRunLayers (spec : RunSpec) : ℕ → Stage → FirstCrossing.Layer → FirstCrossing.Layer
  | 0, _, rows => rows
  | k + 1, stage, rows => match spec.schedule[stage.tick]? with
    | none => []
    | some side => replayRunLayers spec k (stage.next side) (replayNextLayer spec stage rows)

/-- Every replay horizon equals the existing reference layer computation. -/
theorem replayRunLayers_eq (spec : RunSpec) (k : ℕ) (stage : Stage)
    (rows : FirstCrossing.Layer) :
    replayRunLayers spec k stage rows = runLayers spec k stage rows := by
  induction k generalizing stage rows with
  | zero => rfl
  | succ k ih =>
    simp only [replayRunLayers, runLayers, replayNextLayer_eq, ih]
    rfl

/-- Preserve unbonused terminal returns and the single exact HIGH contribution. -/
def replaySector (spec : RunSpec) : Counts :=
  if spec.valid then
    let raw := sectorTerminal spec
      (replayRunLayers spec (2 * spec.n) ⟨0, 0, 0⟩ [(Key.empty, (1, 0))])
    (raw.1, raw.2 + spec.lowerBonus * raw.1)
  else (0, 0)

/-- Sector replay is the actual reference, including its validity guard and bonus. -/
theorem replaySector_eq (spec : RunSpec) : replaySector spec = runSector spec := by
  simp only [replaySector, replayRunLayers_eq, runSector]

/-- Joint replay uses the existing canonical sector order and explicit public zeros. -/
def replayJoint (n : ℕ) : Counts :=
  if n = 0 then (0, 1) else
    (sectorSpecs n (n / 2 + 1)).foldl (fun total spec =>
      let c := replaySector spec
      (total.1 + c.1, total.2 + c.2)) (0, 0)

/-- Both replay channels are exactly the existing joint evaluator channels. -/
theorem replayJoint_eq (n : ℕ) :
    replayJoint n = ((evaluate n).closed, (evaluate n).openEven) := by
  by_cases hn : n = 0
  · simp [replayJoint, evaluate, hn]
  · simp [replayJoint, evaluate, hn, replaySector_eq, runAtThreshold]

/-- The unchanged public parity dispatch, using only the proved reducible joint computation. -/
def replayCount : Problem → ℕ → ℕ
  | .closed, n => (replayJoint n).1
  | .open, q => if q = 0 then 1 else if q % 2 = 1 then (replayJoint (q / 2 + 1)).1
      else (replayJoint (q / 2)).2

/-- Public replay and the registered native counter agree at every index. -/
theorem replayCount_eq (p : Problem) (n : ℕ) : replayCount p n = FirstCrossing.count p n := by
  cases p <;> simp only [replayCount, replayJoint_eq, FirstCrossing.count]

end Meanders.Certify.FirstCrossingRun

namespace Meanders.Certify

/-- Kernel reduction of the equivalent reference establishes an existing count claim. -/
theorem CountCertificate.correct_of_firstCrossingCount (c : CountCertificate)
    (h : FirstCrossingRun.replayCount c.problem c.n = c.count) :
    c.Correct :=
  h.symm.trans ((FirstCrossingRun.replayCount_eq c.problem c.n).trans
    (FirstCrossing.count_eq c.problem c.n))

end Meanders.Certify
