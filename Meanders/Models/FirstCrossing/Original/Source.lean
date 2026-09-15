import Meanders.Core.Matching.Dyck

/-!
# First-height source partition

The original chronological down counters determine the joint height grade.
Every ordered matching pair is either below the threshold everywhere or has
one first hitting cut, with its two owner heights. Connectivity is not used.
-/

namespace Meanders.FirstCrossing

open DyckStep

/-- The two inward-reading sides of a physical cut. -/
inductive Side
  | left
  | right
  deriving DecidableEq, Repr

/-- Source classes before imposing connectivity. Owner heights remain oriented. -/
inductive Sector
  | low
  | high (cut upper lower : ℕ)
  deriving DecidableEq, Repr

/-- Original down-steps before a chronological cut. -/
def downs (w : List DyckStep) (i : ℕ) : ℕ := (w.take i).count D

/-- Joint chronological grade, expressed without division or truncated subtraction. -/
def grade {n : ℕ} (P Q : NoncrossingMatching n) (i : ℕ) : ℤ :=
  (i : ℤ) - downs P.wordOf i - downs Q.wordOf i

/-- Every chronological cut stays strictly below the chosen threshold. -/
def Low {n : ℕ} (K : ℕ) (P Q : NoncrossingMatching n) : Prop :=
  ∀ i, i ≤ 2 * n → grade P Q i < K

/-- The first attainment of the threshold, in original physical coordinates. -/
def FirstHit {n : ℕ} (K : ℕ) (P Q : NoncrossingMatching n) (L : ℕ) : Prop :=
  L ≤ 2 * n ∧ grade P Q L = K ∧ ∀ i, i < L → grade P Q i < K

/-- A complete source pair belongs to one LOW or oriented HIGH sector. -/
def InSector {n : ℕ} (K : ℕ) (P Q : NoncrossingMatching n) : Sector → Prop
  | .low => Low K P Q
  | .high L u v => FirstHit K P Q L ∧ height P.wordOf L = u ∧ height Q.wordOf L = v

instance {n : ℕ} (K : ℕ) (P Q : NoncrossingMatching n) : Decidable (Low K P Q) := by
  unfold Low
  infer_instance

instance {n : ℕ} (K : ℕ) (P Q : NoncrossingMatching n) (L : ℕ) :
    Decidable (FirstHit K P Q L) := by
  unfold FirstHit
  infer_instance

instance {n : ℕ} (K : ℕ) (P Q : NoncrossingMatching n) (s : Sector) :
    Decidable (InSector K P Q s) := by
  cases s <;> unfold InSector <;> infer_instance

/-- Candidate HIGH metadata, including candidates whose source class is empty. -/
def Admissible (n K L u v : ℕ) : Prop :=
  L ≤ 2 * n ∧ u ≤ min L (2 * n - L) ∧ v ≤ min L (2 * n - L) ∧
    u % 2 = L % 2 ∧ v % 2 = L % 2 ∧ u + v = 2 * K

instance {n K L u v : ℕ} : Decidable (Admissible n K L u v) := by
  unfold Admissible
  infer_instance

/-- The fixed asymmetric schedule; midpoint ties read left first. -/
def Sector.schedule (n : ℕ) : Sector → List Side
  | .low => List.replicate (2 * n) .left
  | .high L _ _ =>
    let delta := if L ≤ n then n - L else L - n
    let long := if L < n then Side.right else Side.left
    let short := if L < n then Side.left else Side.right
    List.replicate delta long ++
      (List.replicate (n - delta) [long, short]).flatten ++ List.replicate delta long

/-- The four prescribed down budgets, in PL, PR, QL, QR order. -/
def Sector.budgets (n : ℕ) : Sector → ℕ × ℕ × ℕ × ℕ
  | .low => (n, 0, n, 0)
  | .high L u v => ((L - u) / 2, (2 * n - L - u) / 2,
      (L - v) / 2, (2 * n - L - v) / 2)

/-- Physical height uses original counters, irrespective of any frontier contraction. -/
theorem height_eq_original_downs (w : List DyckStep) (i : ℕ) (hi : i ≤ w.length) :
    height w i = (i : ℤ) - 2 * downs w i := by
  have hc := count_U_add_count_D (w.take i)
  rw [List.length_take, Nat.min_eq_left hi] at hc
  simp only [height, downs]
  omega

/-- The counter grade is half the sum of original owner heights. -/
theorem twice_grade {n : ℕ} (P Q : NoncrossingMatching n) {i : ℕ} (hi : i ≤ 2 * n) :
    2 * grade P Q i = height P.wordOf i + height Q.wordOf i := by
  rw [height_eq_original_downs _ _ (by simpa using hi),
    height_eq_original_downs _ _ (by simpa using hi)]
  simp only [grade]
  ring

@[simp] theorem grade_zero {n : ℕ} (P Q : NoncrossingMatching n) : grade P Q 0 = 0 := by
  simp [grade, downs]

/-- A physical step cannot skip an integer threshold upward. -/
theorem grade_succ_le {n : ℕ} (P Q : NoncrossingMatching n) (i : ℕ) :
    grade P Q (i + 1) ≤ grade P Q i + 1 := by
  simp only [grade, downs, List.take_add_one, List.count_append, Nat.cast_add, Nat.cast_one]
  have hp : 0 ≤ ((P.wordOf[i]?.toList.count D : ℕ) : ℤ) := Int.natCast_nonneg _
  have hq : 0 ≤ ((Q.wordOf[i]?.toList.count D : ℕ) : ℤ) := Int.natCast_nonneg _
  omega

/-- No positive threshold is attained at the final chronological cut. -/
@[simp] theorem grade_end {n : ℕ} (P Q : NoncrossingMatching n) : grade P Q (2 * n) = 0 := by
  have h := twice_grade P Q (le_refl (2 * n))
  have hp := P.isDyck_wordOf.2.1
  have hq := Q.isDyck_wordOf.2.1
  omega

/-- A first hitting cut is unique, even before its owner heights are recorded. -/
theorem firstHit_unique {n K L M : ℕ} {P Q : NoncrossingMatching n}
    (hL : FirstHit K P Q L) (hM : FirstHit K P Q M) : L = M := by
  rcases hL with ⟨_, hL, hpL⟩
  rcases hM with ⟨_, hM, hpM⟩
  rcases lt_trichotomy L M with h | h | h
  · have := hpM L h; omega
  · exact h
  · have := hpL M h; omega

/-- LOW and every HIGH sector are pairwise disjoint. -/
theorem inSector_unique {n K : ℕ} {P Q : NoncrossingMatching n} {s t : Sector}
    (hs : InSector K P Q s) (ht : InSector K P Q t) : s = t := by
  cases s with
  | low =>
    cases t with
    | low => rfl
    | high L u v =>
      obtain ⟨⟨hL, heq, _⟩, _, _⟩ := ht
      have := hs L hL
      omega
  | high L u v =>
    cases t with
    | low =>
      obtain ⟨⟨hL, heq, _⟩, _, _⟩ := hs
      have := ht L hL
      omega
    | high M u' v' =>
      obtain ⟨hL, hu, hv⟩ := hs
      obtain ⟨hM, hu', hv'⟩ := ht
      have : L = M := firstHit_unique hL hM
      subst M
      have : u = u' := by omega
      have : v = v' := by omega
      congr

/-- Every ordered source has one LOW or first-hit HIGH classification. -/
theorem firstHeightPartition {n : ℕ} (K : ℕ) (hK : 0 < K)
    (P Q : NoncrossingMatching n) : ∃! s, InSector K P Q s := by
  classical
  by_cases hlow : Low K P Q
  · exact ⟨.low, hlow, fun _ hs => inSector_unique hs hlow⟩
  · have hex : ∃ i, i ≤ 2 * n ∧ (K : ℤ) ≤ grade P Q i := by
      simpa only [Low, not_forall, not_lt, exists_prop] using hlow
    let L := Nat.find hex
    have hL := Nat.find_spec hex
    have hbefore : ∀ i, i < L → grade P Q i < K := by
      intro i hi
      have := Nat.find_min hex hi
      have : i ≤ 2 * n := by dsimp [L] at hi; omega
      omega
    have hpos : 0 < L := by
      by_contra h
      have hz : L = 0 := by omega
      change L ≤ 2 * n ∧ (K : ℤ) ≤ grade P Q L at hL
      rw [hz, grade_zero] at hL
      omega
    have heq : grade P Q L = K := by
      have hp := hbefore (L - 1) (by omega)
      have hs := grade_succ_le P Q (L - 1)
      rw [Nat.sub_add_cancel hpos] at hs
      change L ≤ 2 * n ∧ (K : ℤ) ≤ grade P Q L at hL
      omega
    let u := (height P.wordOf L).toNat
    let v := (height Q.wordOf L).toNat
    have hu : height P.wordOf L = (u : ℤ) :=
      (Int.toNat_of_nonneg (P.isDyck_wordOf.height_nonneg L)).symm
    have hv : height Q.wordOf L = (v : ℤ) :=
      (Int.toNat_of_nonneg (Q.isDyck_wordOf.height_nonneg L)).symm
    have hs : InSector K P Q (.high L u v) := ⟨⟨hL.1, heq, hbefore⟩, hu, hv⟩
    exact ⟨.high L u v, hs, fun _ ht => inSector_unique ht hs⟩

end Meanders.FirstCrossing
