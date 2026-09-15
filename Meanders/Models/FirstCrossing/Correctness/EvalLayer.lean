import Meanders.Models.FirstCrossing.Native.Eval

/-! Local row-mass conservation. These statements assume no source interpretation. -/
namespace Meanders.FirstCrossing

/-- Additive row observation, used for both stored channels and later continuations. -/
def rowValue (f : Key → Counts → ℕ) (rows : Layer) : ℕ :=
  (rows.map (fun row => f row.1 row.2)).sum

/-- Adjacent aggregation preserves any additive row observation. -/
theorem rowValue_mergeRun (f : Key → Counts → ℕ)
    (hadd : ∀ x a b, f x (a.1 + b.1, a.2 + b.2) = f x a + f x b)
    (row : Row) (rows : Layer) :
    rowValue f (mergeRun row rows) = f row.1 row.2 + rowValue f rows := by
  induction rows generalizing row with
  | nil => simp [mergeRun, rowValue]
  | cons p ps ih =>
    by_cases he : row.1 = p.1
    · rw [mergeRun, ite_eq_left he, ih]
      simp only [hadd]
      simp [rowValue, he, Nat.add_assoc]
    · rw [mergeRun, ite_eq_right he]
      change f row.1 row.2 + rowValue f (mergeRun p ps) = _
      rw [ih]
      simp [rowValue]

/-- Sorting and run merging preserve exact row mass; no hashing assumption is used. -/
theorem rowValue_mergeRows (f : Key → Counts → ℕ)
    (hadd : ∀ x a b, f x (a.1 + b.1, a.2 + b.2) = f x a + f x b)
    (rows : Layer) : rowValue f (mergeRows rows) = rowValue f rows := by
  have hp := ((List.mergeSort_perm rows
    (fun a b => codeLE a.1.sortCode b.1.sortCode)).map
      (fun row => f row.1 row.2)).sum_eq
  unfold mergeRows
  cases hs : rows.mergeSort (fun a b => codeLE a.1.sortCode b.1.sortCode) with
  | nil => simpa [rowValue, hs] using hp
  | cons p ps =>
    rw [rowValue_mergeRun f hadd]
    simpa [rowValue, hs] using hp

/-- A labelled successor's exact weighted contribution, including its lower event. -/
def edgeValue (f : Key → Counts → ℕ) (s : RunSpec) (t : Stage)
    (row : Row) (m : Move) : ℕ :=
  match step s t row.1 m with
  | none => 0
  | some (key, a) => f key (row.2.1, row.2.2 + a * row.2.1)

theorem rowValue_emitMove (f : Key → Counts → ℕ) (s : RunSpec) (t : Stage)
    (row : Row) (m : Move) :
    rowValue f (emitMove s t row m) = edgeValue f s t row m := by
  cases h : step s t row.1 m <;> simp [emitMove, edgeValue, h, rowValue]

/-- Flat emission sums all labels without identifying destination collisions. -/
theorem rowValue_emitRow (f : Key → Counts → ℕ) (s : RunSpec) (t : Stage)
    (row : Row) :
    rowValue f (emitRow s t row) = (Move.all.map (edgeValue f s t row)).sum := by
  simp [emitRow, Move.all, rowValue, List.sum_append, ← rowValue_emitMove]

/-- One layer is precisely the full weighted sum of its four labelled successors. -/
theorem rowValue_nextLayer (f : Key → Counts → ℕ)
    (hadd : ∀ x a b, f x (a.1 + b.1, a.2 + b.2) = f x a + f x b)
    (s : RunSpec) (t : Stage) (rows : Layer) :
    rowValue f (nextLayer s t rows) =
      (rows.map (fun row => (Move.all.map (edgeValue f s t row)).sum)).sum := by
  rw [nextLayer, rowValue_mergeRows f hadd]
  induction rows with
  | nil => simp [rowValue]
  | cons row rows ih =>
    simp only [List.flatMap_cons, rowValue, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] at ih ⊢
    change rowValue f (emitRow s t row) + _ = _
    rw [rowValue_emitRow, ih]

theorem codeLE_total (a b : List ℕ) : codeLE a b = true ∨ codeLE b a = true := by
  induction a generalizing b with
  | nil => exact Or.inl rfl
  | cons a as ih =>
    cases b with
    | nil => exact Or.inr rfl
    | cons b bs =>
      by_cases h : a = b
      · subst b; simpa [codeLE] using ih bs
      · simp only [codeLE, h, Ne.symm h, reduceIte, decide_eq_true_eq]
        omega

theorem codeLE_trans {a b c : List ℕ} (hab : codeLE a b = true)
    (hbc : codeLE b c = true) : codeLE a c = true := by
  induction a generalizing b c with
  | nil => rfl
  | cons a as ih =>
    cases b with
    | nil => simp [codeLE] at hab
    | cons b bs =>
      cases c with
      | nil => simp [codeLE] at hbc
      | cons c cs =>
        by_cases hab' : a = b
        · subst b
          by_cases hbc' : a = c
          · subst c
            simpa [codeLE] using ih (by simpa [codeLE] using hab) (by simpa [codeLE] using hbc)
          · simpa [codeLE, hbc'] using hbc
        · by_cases hbc' : b = c
          · subst c; simpa [codeLE, hab'] using hab
          · have hlt : a < c := by
              simp only [codeLE, hab', hbc', reduceIte, decide_eq_true_eq] at hab hbc
              omega
            simp [codeLE, Nat.ne_of_lt hlt, hlt]

theorem codeLE_antisymm {a b : List ℕ} (hab : codeLE a b = true)
    (hba : codeLE b a = true) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [codeLE]
  | cons a as ih =>
    cases b with
    | nil => simp [codeLE] at hab
    | cons b bs =>
      by_cases h : a = b
      · subst b; simpa [codeLE] using ih (by simpa [codeLE] using hab)
          (by simpa [codeLE] using hba)
      · simp only [codeLE, h, Ne.symm h, reduceIte, decide_eq_true_eq] at hab hba
        omega

/-- Canonical non-strict ordering of the complete keys. -/
def Key.LE (a b : Key) : Prop := codeLE a.sortCode b.sortCode = true

theorem Key.le_antisymm {a b : Key} (hab : a.LE b) (hba : b.LE a) : a = b :=
  Key.sortCode_injective (codeLE_antisymm hab hba)

/-- Every merged output key came from the input, irrespective of weights. -/
theorem mergeRun_key_mem {row : Row} {rows : Layer} {out : Row}
    (h : out ∈ mergeRun row rows) : out.1 = row.1 ∨ ∃ p ∈ rows, out.1 = p.1 := by
  induction rows generalizing row with
  | nil =>
    have he : out = row := by simpa [mergeRun] using h
    exact Or.inl (congrArg Prod.fst he)
  | cons p ps ih =>
    by_cases he : row.1 = p.1
    · rw [mergeRun, ite_eq_left he] at h
      rcases ih h with h | ⟨q, hq, heq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, List.mem_cons_of_mem p hq, heq⟩
    · rw [mergeRun, ite_eq_right he] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inl rfl
      · rcases ih h with h | ⟨q, hq, heq⟩
        · exact Or.inr ⟨p, List.mem_cons_self, h⟩
        · exact Or.inr ⟨q, List.mem_cons_of_mem p hq, heq⟩

/-- Ordered runs never emit a key twice. -/
theorem mergeRun_nodup (row : Row) (rows : Layer)
    (h : (row :: rows).Pairwise (fun a b => a.1.LE b.1)) :
    ((mergeRun row rows).map Prod.fst).Nodup := by
  induction rows generalizing row with
  | nil => simp [mergeRun]
  | cons p ps ih =>
    obtain ⟨hrow, hp⟩ := List.pairwise_cons.mp h
    by_cases he : row.1 = p.1
    · rw [mergeRun, ite_eq_left he]
      apply ih
      exact List.pairwise_cons.mpr
        ⟨fun q hq => hrow q (List.mem_cons_of_mem p hq), hp.tail⟩
    · rw [mergeRun, ite_eq_right he, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih p hp⟩
      intro hm
      obtain ⟨out, hout, heq⟩ := List.mem_map.mp hm
      rcases mergeRun_key_mem hout with ho | ⟨q, hq, ho⟩
      · exact he (heq.symm.trans ho)
      · have hpq := (List.pairwise_cons.mp hp).1 q hq
        have hrp := hrow p List.mem_cons_self
        have hqr : q.1 = row.1 := ho.symm.trans heq
        rw [hqr] at hpq
        exact he (Key.le_antisymm hrp hpq)

/-- Sorting uses the proved deterministic total and transitive full-key order. -/
theorem emitted_sorted (rows : Layer) :
    (rows.mergeSort (fun a b => codeLE a.1.sortCode b.1.sortCode)).Pairwise
      (fun a b => a.1.LE b.1) := by
  apply List.pairwise_mergeSort
  · intro a b c hab hbc; exact codeLE_trans hab hbc
  · intro a b
    exact Bool.or_eq_true_iff.mpr (codeLE_total a.1.sortCode b.1.sortCode)

theorem mergeRows_nodup (rows : Layer) : ((mergeRows rows).map Prod.fst).Nodup := by
  have h := emitted_sorted rows
  unfold mergeRows
  cases hs : rows.mergeSort (fun a b => codeLE a.1.sortCode b.1.sortCode) with
  | nil => simp
  | cons row rest => exact mergeRun_nodup row rest (hs ▸ h)

theorem nextLayer_nodup (s : RunSpec) (t : Stage) (rows : Layer) :
    ((nextLayer s t rows).map Prod.fst).Nodup := mergeRows_nodup _

end Meanders.FirstCrossing
