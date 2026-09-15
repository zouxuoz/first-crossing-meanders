import Meanders.Models.FirstCrossing.Original.Source
import Meanders.Models.FirstCrossing.Original.Cut

/-!
# Admissible first-height sectors and their schedules

Actual source sectors satisfy the prescribed ballot budgets. Their asymmetric
schedule reads each physical side exactly once, including midpoint ties.
-/

namespace Meanders.FirstCrossing

/-- Actual HIGH sources satisfy all candidate metadata constraints. -/
theorem inSector_high_admissible {n K L u v : ℕ} {P Q : NoncrossingMatching n}
    (hs : InSector K P Q (.high L u v)) : Admissible n K L u v := by
  obtain ⟨hit, hu, hv⟩ := hs
  let pl := leftHalf hit.1 (⟨P, hu⟩ : MatchingAtCut n L u)
  let pr := rightHalf hit.1 (⟨P, hu⟩ : MatchingAtCut n L u)
  let ql := leftHalf hit.1 (⟨Q, hv⟩ : MatchingAtCut n L v)
  let qr := rightHalf hit.1 (⟨Q, hv⟩ : MatchingAtCut n L v)
  have hpl := pl.height_le_length
  have hpr := pr.height_le_length
  have hql := ql.height_le_length
  have hqr := qr.height_le_length
  have hp := pl.length_eq_height_add_twice_down
  have hq := ql.length_eq_height_add_twice_down
  have hg := twice_grade P Q hit.1
  rw [hit.2.1, hu, hv] at hg
  refine ⟨hit.1, (Nat.le_min.mpr ⟨hpl, hpr⟩), (Nat.le_min.mpr ⟨hql, hqr⟩), ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

/-- Positive first hits occur strictly inside the chronological word. -/
theorem firstHit_interior {n K L : ℕ} {P Q : NoncrossingMatching n}
    (hK : 0 < K) (hit : FirstHit K P Q L) : 0 < L ∧ L < 2 * n := by
  have hzero := grade_zero P Q
  have hend := grade_end P Q
  obtain ⟨hL, heq, _⟩ := hit
  constructor
  · by_contra h
    have : L = 0 := by omega
    subst L
    omega
  · by_contra h
    have : L = 2 * n := by omega
    rw [this] at heq
    omega

/-- The unpaired prefix length is bounded by the threshold slack. -/
theorem Admissible.delta_le {n K L u v : ℕ} (hs : Admissible n K L u v) :
    (if L ≤ n then n - L else L - n) ≤ n - K := by
  unfold Admissible at hs
  split_ifs <;> omega

/-- Alternating side pairs contribute exactly two visits per repetition. -/
theorem length_alternating (k : ℕ) (a b : Side) :
    ((List.replicate k [a, b]).flatten).length = 2 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.length_append,
      List.length_cons, List.length_nil, ih]
    omega

/-- Each repeated side pair contributes its exact labelled visit multiplicity. -/
theorem count_alternating (k : ℕ) (a b s : Side) :
    ((List.replicate k [a, b]).flatten).count s =
      k * ([a, b].count s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.count_append, ih,
      Nat.succ_mul]
    omega

@[simp] theorem Sector.schedule_low (n : ℕ) :
    Sector.low.schedule n = List.replicate (2 * n) Side.left := rfl

/-- HIGH schedules contain exactly the physical number of vertices. -/
theorem Sector.schedule_high_length {n L u v : ℕ} (hL : L ≤ 2 * n) :
    ((Sector.high L u v).schedule n).length = 2 * n := by
  simp only [Sector.schedule, List.length_append, List.length_replicate,
    length_alternating]
  split_ifs <;> omega

/-- The left side is read exactly up to the cut. -/
theorem Sector.schedule_high_count_left {n L u v : ℕ} (hL : L ≤ 2 * n) :
    ((Sector.high L u v).schedule n).count Side.left = L := by
  simp only [Sector.schedule, List.count_append, count_alternating]
  split_ifs <;> simp_all [List.count_replicate] <;> omega

/-- The right side is read exactly from the endpoint back to the cut. -/
theorem Sector.schedule_high_count_right {n L u v : ℕ} (hL : L ≤ 2 * n) :
    ((Sector.high L u v).schedule n).count Side.right = 2 * n - L := by
  simp only [Sector.schedule, List.count_append, count_alternating]
  split_ifs <;> simp_all [List.count_replicate] <;> omega

end Meanders.FirstCrossing
