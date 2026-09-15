import Meanders.Models.FirstCrossing.Correctness.EvalLayer

/-! Exact labelled-history interpretation of the shared paired layer recurrence. -/
namespace Meanders.FirstCrossing

/-- Every length-k move word, retaining all four labels and their multiplicities. -/
def labelWords (k : ℕ) : List (List Move) := wordsOver Move.all k

theorem labelWords_succ (k : ℕ) : labelWords (k + 1) =
    Move.all.flatMap (fun m => (labelWords k).map (m :: ·)) := rfl

@[simp] theorem mem_labelWords {labels : List Move} {k : ℕ} :
    labels ∈ labelWords k ↔ labels.length = k :=
  mem_wordsOver (fun m => by cases m <;> simp [Move.all])

theorem labelWords_nodup (k : ℕ) : (labelWords k).Nodup :=
  nodup_wordsOver (by simp [Move.all]) k

/-- Interpret labels through the actual native step, accumulating its exact lower event. -/
def followLabels (spec : RunSpec) : Stage → Key → List Move → Option (Key × ℕ)
  | _, key, [] => some (key, 0)
  | t, key, m :: ms => do
    let side ← spec.schedule[t.tick]?
    let (next, a) ← step spec t key m
    let (last, b) ← followLabels spec (t.next side) next ms
    return (last, a + b)

/-- A labelled history transports arbitrary starting ordinary/lower mass exactly. -/
def labelValue (f : Key → Counts → ℕ) (spec : RunSpec) (t : Stage)
    (row : Row) (labels : List Move) : ℕ :=
  match followLabels spec t row.1 labels with
  | none => 0
  | some (last, a) => f last (row.2.1, row.2.2 + a * row.2.1)

/-- The finite sum over all labelled histories from one row. -/
def historiesValue (f : Key → Counts → ℕ) (spec : RunSpec) (k : ℕ)
    (t : Stage) (key : Key) (c : Counts) : ℕ :=
  ((labelWords k).map (labelValue f spec t (key, c))).sum

/-- A fixed labelled history acts linearly on the two initial weight channels. -/
theorem labelValue_add (f : Key → Counts → ℕ)
    (hadd : ∀ x a b, f x (a.1 + b.1, a.2 + b.2) = f x a + f x b)
    (spec : RunSpec) (t : Stage) (key : Key) (a b : Counts) (labels : List Move) :
    labelValue f spec t (key, (a.1 + b.1, a.2 + b.2)) labels =
      labelValue f spec t (key, a) labels + labelValue f spec t (key, b) labels := by
  unfold labelValue
  cases he : followLabels spec t key labels with
  | none => rfl
  | some out =>
    rcases out with ⟨last, e⟩
    have hp : a.2 + b.2 + e * (a.1 + b.1) = (a.2 + e * a.1) + (b.2 + e * b.1) := by ring
    simpa only [hp] using hadd last (a.1, a.2 + e * a.1) (b.1, b.2 + e * b.1)

theorem historiesValue_add (f : Key → Counts → ℕ)
    (hadd : ∀ x a b, f x (a.1 + b.1, a.2 + b.2) = f x a + f x b)
    (spec : RunSpec) (k : ℕ) (t : Stage) (key : Key) (a b : Counts) :
    historiesValue f spec k t key (a.1 + b.1, a.2 + b.2) =
      historiesValue f spec k t key a + historiesValue f spec k t key b := by
  unfold historiesValue
  rw [← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro labels _
  exact labelValue_add f hadd spec t key a b labels

@[simp] theorem historiesValue_zero (f : Key → Counts → ℕ) (spec : RunSpec)
    (t : Stage) (key : Key) (c : Counts) : historiesValue f spec 0 t key c = f key c := by
  simp [historiesValue, labelWords, wordsOver, labelValue, followLabels]

/-- Consuming one scheduled label matches exactly the row emitted by the paired step. -/
theorem labelValue_cons (f : Key → Counts → ℕ) (spec : RunSpec) (t : Stage)
    (row : Row) (m : Move) (labels : List Move) {side : Side}
    (hs : spec.schedule[t.tick]? = some side) :
    labelValue f spec t row (m :: labels) =
      rowValue (fun key c => labelValue f spec (t.next side) (key, c) labels)
        (emitMove spec t row m) := by
  cases he : step spec t row.1 m with
  | none => simp [labelValue, followLabels, hs, he, emitMove, rowValue]
  | some out =>
    rcases out with ⟨key, a⟩
    cases hf : followLabels spec (t.next side) key labels with
    | none => simp [labelValue, followLabels, hs, he, hf, emitMove, rowValue]
    | some last =>
      rcases last with ⟨key', b⟩
      simp [labelValue, followLabels, hs, he, hf, emitMove, rowValue, Option.bind_eq_bind]
      congr 2
      ring

/-- With no remaining scheduled side, every positive-length history rejects. -/
theorem historiesValue_no_side (f : Key → Counts → ℕ) (spec : RunSpec) (k : ℕ)
    (t : Stage) (key : Key) (c : Counts) (hs : spec.schedule[t.tick]? = none) :
    historiesValue f spec (k + 1) t key c = 0 := by
  simp [historiesValue, labelWords, wordsOver, Move.all, List.map_map, Function.comp_def,
    labelValue, followLabels,
    hs, Option.bind_eq_bind]

private theorem historiesValue_move (f : Key → Counts → ℕ) (spec : RunSpec) (k : ℕ)
    (t : Stage) (row : Row) (m : Move) {side : Side}
    (hs : spec.schedule[t.tick]? = some side) :
    ((labelWords k).map (fun labels => labelValue f spec t row (m :: labels))).sum =
      rowValue (historiesValue f spec k (t.next side)) (emitMove spec t row m) := by
  cases he : step spec t row.1 m with
  | none =>
    simp [labelValue_cons f spec t row m _ hs, emitMove, he, rowValue]
  | some out =>
    rcases out with ⟨key, a⟩
    simp [labelValue_cons f spec t row m _ hs, emitMove, he, rowValue, historiesValue]

/-- One native visit partitions labelled words by their first label. -/
theorem historiesValue_succ (f : Key → Counts → ℕ) (spec : RunSpec) (k : ℕ)
    (t : Stage) (row : Row) {side : Side} (hs : spec.schedule[t.tick]? = some side) :
    historiesValue f spec (k + 1) t row.1 row.2 =
      rowValue (historiesValue f spec k (t.next side)) (emitRow spec t row) := by
  change ((labelWords (k + 1)).map (labelValue f spec t row)).sum = _
  simp only [labelWords_succ, Move.all, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.map_append, List.sum_append, List.map_map, Function.comp_def]
  rw [historiesValue_move f spec k t row .UU hs,
    historiesValue_move f spec k t row .UD hs,
    historiesValue_move f spec k t row .DU hs,
    historiesValue_move f spec k t row .DD hs]
  simp [emitRow, Move.all, rowValue, List.sum_append]

/-- A merged layer preserves the exact finite labelled-history value for the suffix. -/
theorem jointLayer_invariant (f : Key → Counts → ℕ)
    (hadd : ∀ x a b, f x (a.1 + b.1, a.2 + b.2) = f x a + f x b)
    (spec : RunSpec) (k : ℕ) (t : Stage) (rows : Layer) {side : Side}
    (hs : spec.schedule[t.tick]? = some side) :
    rowValue (historiesValue f spec k (t.next side)) (nextLayer spec t rows) =
      rowValue (historiesValue f spec (k + 1) t) rows := by
  rw [nextLayer, rowValue_mergeRows _ (historiesValue_add f hadd spec k (t.next side))]
  induction rows with
  | nil => simp [rowValue]
  | cons row rows ih =>
    simp only [List.flatMap_cons, rowValue, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons] at ih ⊢
    change rowValue (historiesValue f spec k (t.next side)) (emitRow spec t row) + _ = _
    rw [← historiesValue_succ f spec k t row hs, ih]

/-- The paired native runner equals the exact sum of its accepted labelled histories. -/
theorem runLayers_histories (f : Key → Counts → ℕ)
    (hadd : ∀ x a b, f x (a.1 + b.1, a.2 + b.2) = f x a + f x b)
    (spec : RunSpec) (k : ℕ) (t : Stage) (rows : Layer) :
    rowValue f (runLayers spec k t rows) = rowValue (historiesValue f spec k t) rows := by
  induction k generalizing t rows with
  | zero => simp [runLayers, rowValue]
  | succ k ih =>
    rw [runLayers]
    cases hs : spec.schedule[t.tick]? with
    | none => simp [rowValue, historiesValue_no_side f spec k t _ _ hs]
    | some side =>
      rw [ih]
      exact jointLayer_invariant f hadd spec k t rows hs

/-- From the single empty history, the full run is its accepted word sum. -/
theorem runLayers_seed (f : Key → Counts → ℕ)
    (hadd : ∀ x a b, f x (a.1 + b.1, a.2 + b.2) = f x a + f x b)
    (spec : RunSpec) :
    rowValue f (runLayers spec (2 * spec.n) ⟨0, 0, 0⟩ [(Key.empty, (1, 0))]) =
      historiesValue f spec (2 * spec.n) ⟨0, 0, 0⟩ Key.empty (1, 0) := by
  rw [runLayers_histories f hadd]
  simp [rowValue]

end Meanders.FirstCrossing
