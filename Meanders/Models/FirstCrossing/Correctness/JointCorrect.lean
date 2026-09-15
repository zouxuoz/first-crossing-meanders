import Meanders.Models.FirstCrossing.Correctness.EvalCorrect
import Meanders.Models.FirstCrossing.Correctness.ClosedBridge
import Meanders.Models.FirstCrossing.Correctness.SourceCounts

/-! Unconditional correctness of the native reference through the connected source bijection. -/
namespace Meanders.FirstCrossing

/-- The actual accepted-source bijection identifies both terminal sector outputs. -/
theorem runSector_correct {spec : RunSpec} (hv : spec.valid = true) :
    (runSector spec).1 = Fintype.card (ConnectedSource spec) ∧
      (runSector spec).2 =
        ∑ source : ConnectedSource spec, source.val.matchings.2.exteriorArches.card := by
  classical
  constructor
  · rw [runSector_eq_card_accepted hv]
    exact Fintype.card_congr (acceptedSourceEquiv spec hv)
  · rw [runSector_eq_sum_exterior hv]
    exact Fintype.sum_equiv (acceptedSourceEquiv spec hv) _ _ (fun _ => rfl)

/-- Every valid threshold computes the canonical closed and even-open numbers jointly. -/
theorem evaluateJoint_correct {n K : ℕ} (hn : 0 < n) (hK : 0 < K) (hKn : K ≤ n) :
    runAtThreshold n K = (closedMeanderNumber n, openMeanderNumber (2 * n)) := by
  classical
  rw [runAtThreshold_pair]
  apply Prod.ext
  · change ((sectorSpecs n K).map (fun spec => (runSector spec).1)).sum = _
    rw [← sectorSpecs_closed_sum hn hK hKn]
    congr 1
    apply List.map_congr_left
    intro spec hs
    exact (runSector_correct (sectorSpecs_valid hs)).1
  · change ((sectorSpecs n K).map (fun spec => (runSector spec).2)).sum = _
    rw [← sectorSpecs_open_sum hn hK hKn]
    congr 1
    apply List.map_congr_left
    intro spec hs
    exact (runSector_correct (sectorSpecs_valid hs)).2

private theorem closed_number_zero : closedMeanderNumber 0 = 0 := by
  have : IsEmpty (ClosedMeander 0) := ⟨fun p => Fin.elim0 p.property.nonempty.some⟩
  simp [closedMeanderNumber]

/-- The default joint evaluation has the exact public zeros and both positive-rank counts. -/
theorem evaluate_correct (n : ℕ) :
    (evaluate n).closed = closedMeanderNumber n ∧
      (evaluate n).openEven = openMeanderNumber (2 * n) := by
  by_cases hn : n = 0
  · subst n
    simp [evaluate, closed_number_zero]
  · obtain ⟨hK, hKn⟩ := defaultThreshold_valid (Nat.pos_of_ne_zero hn)
    have he := evaluateJoint_correct (Nat.pos_of_ne_zero hn) hK hKn
    simp [evaluate, hn, he]

end Meanders.FirstCrossing
