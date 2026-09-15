import Meanders.Models.FirstCrossing.Interpretation.FIFO

/-!
# Source opening-list updates at a physical step

The source list is the existing matching stack read oldest first. These
lemmas identify the physical endpoint consumed by a close and prove it is
in the unforced reservoir for any feasible original down budget.
-/

namespace Meanders.FirstCrossing

open DyckStep

/-- Original unmatched physical openings, oldest first. -/
def sourceOpeningList {n : ℕ} (m : NoncrossingMatching n) (i : ℕ) : List (Point n) :=
  (m.activeList i).reverse

@[simp] theorem sourceOpeningList_mem {n i : ℕ} (m : NoncrossingMatching n) (a : Point n) :
    a ∈ sourceOpeningList m i ↔ a ∈ m.active i := by
  simp [sourceOpeningList]

/-- This list consists of precisely the actual unmatched openings of the original prefix. -/
theorem sourceOpeningList_mem_word {n i : ℕ} (m : NoncrossingMatching n) (hi : i ≤ 2 * n)
    (a : Point n) :
    a ∈ sourceOpeningList m i ↔ a.val ∈ oldOpenings (m.wordOf.take i) := by
  rw [sourceOpeningList_mem, oldOpenings_matching_prefix m hi a]

/-- The physical source list agrees with sorting the independently defined old opening set. -/
theorem sourceOpeningList_map {n i : ℕ} (m : NoncrossingMatching n) (hi : i ≤ 2 * n) :
    (sourceOpeningList m i).map Fin.val = (oldOpenings (m.wordOf.take i)).sort (· ≤ ·) := by
  classical
  have hnd : ((sourceOpeningList m i).map Fin.val).Nodup := by
    apply List.Nodup.map Fin.val_injective
    simpa only [sourceOpeningList, List.nodup_reverse, NoncrossingMatching.activeList] using
      (m.active i).sort_nodup (· ≥ ·)
  have hp : (sourceOpeningList m i).Pairwise (· ≤ ·) := by
    simpa only [sourceOpeningList, List.pairwise_reverse, NoncrossingMatching.activeList] using
      (m.active i).pairwise_sort (· ≥ ·)
  have hpm : ((sourceOpeningList m i).map Fin.val).Pairwise (· ≤ ·) :=
    List.pairwise_map.mpr hp
  have he : ((sourceOpeningList m i).map Fin.val).toFinset =
      oldOpenings (m.wordOf.take i) := by
    ext l
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (sourceOpeningList_mem_word m hi a).mp ha
    · intro hl
      have hli := (mem_oldOpenings.mp hl).1
      have hln : l < 2 * n := by
        simp only [List.length_take, m.length_wordOf, Nat.min_eq_left hi] at hli
        omega
      let a : Point n := ⟨l, hln⟩
      exact ⟨a, (sourceOpeningList_mem_word m hi a).mpr hl, rfl⟩
  have hs := (List.toFinset_sort (r := (· ≤ ·)) hnd).mpr hpm
  rw [he] at hs
  exact hs.symm

/-- Original source height is the length of the unmatched-opening list. -/
theorem sourceOpeningList_length {n i : ℕ} (m : NoncrossingMatching n) (hi : i ≤ 2 * n) :
    ((sourceOpeningList m i).length : ℤ) = height m.wordOf i := by
  simpa only [sourceOpeningList, List.length_reverse, m.length_activeList] using m.card_active hi

/-- Physical U labels are precisely opening matching endpoints. -/
theorem source_step_U_iff {n : ℕ} (m : NoncrossingMatching n) (v : Point n) :
    m.wordOf[v.val]? = some U ↔ m.opens v := by
  rw [m.getElem?_wordOf v.isLt, m.partnerIndex_coe]
  unfold NoncrossingMatching.opens
  by_cases h : v.val < (m.partner v).val
  · simp [h, show v < m.partner v from h]
  · simp [h, show ¬ v < m.partner v from h]

/-- Physical D labels are precisely closing matching endpoints. -/
theorem source_step_D_iff {n : ℕ} (m : NoncrossingMatching n) (v : Point n) :
    m.wordOf[v.val]? = some D ↔ ¬ m.opens v := by
  rw [m.getElem?_wordOf v.isLt, m.partnerIndex_coe]
  unfold NoncrossingMatching.opens
  by_cases h : v.val < (m.partner v).val
  · simp [h, show v < m.partner v from h]
  · simp [h, show ¬ v < m.partner v from h]

/-- D increases the original down counter once. -/
theorem downs_succ_of_D {w : List DyckStep} {i : ℕ} (hD : w[i]? = some D) :
    downs w (i + 1) = downs w i + 1 := by
  simp [downs, List.take_add_one, List.count_append, hD]

/-- An original U appends the newly opened physical endpoint as the newest opening. -/
theorem sourceOpeningList_succ_U {n : ℕ} (m : NoncrossingMatching n) (v : Point n)
    (hU : m.wordOf[v.val]? = some U) :
    sourceOpeningList m (v.val + 1) = sourceOpeningList m v.val ++ [v] := by
  simp [sourceOpeningList, m.activeList_succ_open ((source_step_U_iff m v).mp hU)]

/-- An original D removes exactly the newest opening, its physical matching partner. -/
theorem sourceOpeningList_succ_D {n : ℕ} (m : NoncrossingMatching n) (v : Point n)
    (hD : m.wordOf[v.val]? = some D) :
    sourceOpeningList m v.val = sourceOpeningList m (v.val + 1) ++ [m.partner v] := by
  simp [sourceOpeningList, m.activeList_succ_close ((source_step_D_iff m v).mp hD)]

/-- A legal D has at least one unforced opening: its original ordinal is at or above E. -/
theorem emitted_le_after_close_length {n A : ℕ} (m : NoncrossingMatching n) (v : Point n)
    (hD : m.wordOf[v.val]? = some D) (hA : downs m.wordOf (v.val + 1) ≤ A) :
    v.val - A - downs m.wordOf v.val ≤ (sourceOpeningList m (v.val + 1)).length := by
  have hl := sourceOpeningList_length m (i := v.val + 1) (by have := v.isLt; omega)
  have hh := height_eq_original_downs m.wordOf (v.val + 1) (by simp)
  rw [downs_succ_of_D hD] at hh hA
  omega

/-- Forgetting any already joined emitted prefix preserves the native newest-first D view. -/
theorem source_close_retained_reverse {n A joined : ℕ}
    (m : NoncrossingMatching n) (v : Point n)
    (hD : m.wordOf[v.val]? = some D) (hA : downs m.wordOf (v.val + 1) ≤ A)
    (hj : joined ≤ v.val - A - downs m.wordOf v.val) :
    ((sourceOpeningList m v.val).drop joined).reverse =
      m.partner v :: ((sourceOpeningList m (v.val + 1)).drop joined).reverse := by
  have hbound := hj.trans (emitted_le_after_close_length m v hD hA)
  rw [sourceOpeningList_succ_D m v hD, List.drop_append,
    Nat.sub_eq_zero_of_le hbound, List.drop_zero]
  simp

/-- U appends its physical endpoint even after an already joined source prefix is forgotten. -/
theorem source_open_retained {n joined : ℕ} (m : NoncrossingMatching n) (v : Point n)
    (hU : m.wordOf[v.val]? = some U) (hj : joined ≤ (sourceOpeningList m v.val).length) :
    (sourceOpeningList m (v.val + 1)).drop joined =
      (sourceOpeningList m v.val).drop joined ++ [v] := by
  rw [sourceOpeningList_succ_U m v hU, List.drop_append,
    Nat.sub_eq_zero_of_le hj, List.drop_zero]

private theorem mem_drop_iff_older_length {α : Type*} [LinearOrder α]
    (xs : List α) (hs : xs.Pairwise (· < ·)) (a : α) (k : ℕ) :
    a ∈ xs.drop k ↔ a ∈ xs ∧ k ≤ (xs.filter (· < a)).length := by
  induction xs generalizing k with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.drop_succ_cons]
      by_cases ha : a ∈ xs
      · have hxa := hhead a ha
        rw [ih htail k]
        simp [ha, hxa]
      · have hdrop : a ∉ xs.drop k := fun hm => ha (List.mem_of_mem_drop hm)
        by_cases hax : a = x
        · subst a
          have hf : xs.filter (· < x) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro y hy
            have hxy := hhead y hy
            simp only [decide_eq_true_eq]
            exact not_lt_of_ge hxy.le
          simp [hdrop, hf]
        · simp [hdrop, ha, hax]

/-- Dropping an oldest prefix retains exactly the active openings at or above its ordinal. -/
theorem sourceOpeningList_mem_drop {n i k : ℕ} (m : NoncrossingMatching n) (a : Point n) :
    a ∈ (sourceOpeningList m i).drop k ↔ a ∈ m.active i ∧
      k ≤ ((m.active i).filter (· < a)).card := by
  classical
  have hn : (sourceOpeningList m i).Nodup := by
    simpa only [sourceOpeningList, List.nodup_reverse, NoncrossingMatching.activeList] using
      (m.active i).sort_nodup (· ≥ ·)
  have hp : (sourceOpeningList m i).Pairwise (· ≤ ·) := by
    simpa only [sourceOpeningList, List.pairwise_reverse, NoncrossingMatching.activeList] using
      (m.active i).pairwise_sort (· ≥ ·)
  have hstrict : (sourceOpeningList m i).Pairwise (· < ·) := by
    have hboth := hp.and hn
    exact hboth.imp fun hh => lt_of_le_of_ne hh.1 hh.2
  have he : (sourceOpeningList m i).toFinset = m.active i := by
    ext b
    simp
  have hc : ((sourceOpeningList m i).filter (· < a)).length =
      ((m.active i).filter (· < a)).card := by
    rw [← List.toFinset_card_of_nodup (hn.filter _), List.toFinset_filter, he]
    simp only [decide_eq_true_eq]
  rw [mem_drop_iff_older_length _ hstrict a k, sourceOpeningList_mem, hc]

/-- The same retained-ordinal criterion in the independently sorted natural-index list. -/
theorem sourceOpeningNat_mem_drop {n i k : ℕ} (m : NoncrossingMatching n)
    (hi : i ≤ 2 * n) (a : Point n) :
    a.val ∈ ((oldOpenings (m.wordOf.take i)).sort (· ≤ ·)).drop k ↔
      a ∈ m.active i ∧ k ≤ ((m.active i).filter (· < a)).card := by
  rw [← sourceOpeningList_map m hi, ← List.map_drop]
  simpa only [List.mem_map, Fin.val_inj, exists_eq_right] using sourceOpeningList_mem_drop m a

end Meanders.FirstCrossing
