import Meanders.Models.FirstCrossing.Correctness.AcceptedWeight

/-! Terminal paired bookkeeping over actual accepted native label words. -/
namespace Meanders.FirstCrossing

/-- Ordinary terminal mass, with the actual terminal key filter. -/
def terminalOrdinary (spec : RunSpec) (key : Key) (c : Counts) : ℕ :=
  if terminalKey spec key then c.1 else 0

/-- Lower terminal mass; the prescribed HIGH bonus is applied only here. -/
def terminalLower (spec : RunSpec) (key : Key) (c : Counts) : ℕ :=
  if terminalKey spec key then c.2 + spec.lowerBonus * c.1 else 0

private theorem terminal_fold (spec : RunSpec) (rows : Layer) (initial : Counts) :
    rows.foldl (fun total row => if terminalKey spec row.1 then
      (total.1 + row.2.1, total.2 + row.2.2) else total) initial =
      (initial.1 + rowValue (terminalOrdinary spec) rows,
        initial.2 + rowValue (fun key c => if terminalKey spec key then c.2 else 0) rows) := by
  induction rows generalizing initial with
  | nil => simp [rowValue]
  | cons row rows ih =>
    rw [List.foldl_cons]
    by_cases h : terminalKey spec row.1 = true
    · simp only [h, ite_true, ih, rowValue, List.map_cons, List.sum_cons, terminalOrdinary]
      simp [Nat.add_assoc]
    · simp only [h, Bool.false_eq_true, ite_false, ih, rowValue,
        List.map_cons, List.sum_cons, terminalOrdinary]
      simp

theorem sectorTerminal_ordinary (spec : RunSpec) (rows : Layer) :
    (sectorTerminal spec rows).1 = rowValue (terminalOrdinary spec) rows := by
  simp [sectorTerminal, terminal_fold]

/-- The separately applied terminal bonus is exactly the additive lower row observation. -/
theorem sectorTerminal_lower (spec : RunSpec) (rows : Layer) :
    (sectorTerminal spec rows).2 + spec.lowerBonus * (sectorTerminal spec rows).1 =
      rowValue (terminalLower spec) rows := by
  simp only [sectorTerminal, terminal_fold, Nat.zero_add]
  induction rows with
  | nil => simp [rowValue]
  | cons row rows ih =>
    simp only [rowValue, List.map_cons, List.sum_cons, terminalOrdinary, terminalLower] at ih ⊢
    by_cases h : terminalKey spec row.1 = true
    · simp only [h, ite_true] at ⊢
      rw [← ih]
      ring
    · simp [h, ih]

theorem terminalOrdinary_add (spec : RunSpec) (key : Key) (a b : Counts) :
    terminalOrdinary spec key (a.1 + b.1, a.2 + b.2) =
      terminalOrdinary spec key a + terminalOrdinary spec key b := by
  by_cases h : terminalKey spec key = true <;> simp [terminalOrdinary, h]

theorem terminalLower_add (spec : RunSpec) (key : Key) (a b : Counts) :
    terminalLower spec key (a.1 + b.1, a.2 + b.2) =
      terminalLower spec key a + terminalLower spec key b := by
  by_cases h : terminalKey spec key = true <;> simp [terminalLower, h]
  ring

/-- Actual ordinary sector output equals the terminal-filtered accepted label-word sum. -/
theorem runSector_ordinary_labels {spec : RunSpec} (hv : spec.valid = true) :
    (runSector spec).1 =
      historiesValue (terminalOrdinary spec) spec (2 * spec.n) ⟨0, 0, 0⟩ Key.empty (1, 0) := by
  simp only [runSector, hv, ite_true]
  rw [sectorTerminal_ordinary]
  exact runLayers_seed _ (terminalOrdinary_add spec) spec

/-- Actual lower sector output uses the same labels and terminal validation, with one bonus. -/
theorem runSector_lower_labels {spec : RunSpec} (hv : spec.valid = true) :
    (runSector spec).2 =
      historiesValue (terminalLower spec) spec (2 * spec.n) ⟨0, 0, 0⟩ Key.empty (1, 0) := by
  simp only [runSector, hv, ite_true]
  rw [sectorTerminal_lower]
  exact runLayers_seed _ (terminalLower_add spec) spec

/-- The accumulated event returned by an accepted word; the fallback is unreachable. -/
def AcceptedWord.eventSum {spec : RunSpec} (word : AcceptedWord spec) : ℕ :=
  ((followLabels spec ⟨0, 0, 0⟩ Key.empty word.val).getD (Key.empty, 0)).2

theorem AcceptedWord.eventSum_eq {spec : RunSpec} (word : AcceptedWord spec) {key : Key} {a : ℕ}
    (hf : followLabels spec ⟨0, 0, 0⟩ Key.empty word.val = some (key, a)) :
    word.eventSum = a := by simp [AcceptedWord.eventSum, hf]

/-- Actual ordinary output is the cardinality of the independently recognized accepted words. -/
theorem runSector_eq_card_accepted {spec : RunSpec} (hv : spec.valid = true) :
    (runSector spec).1 = Fintype.card (AcceptedWord spec) := by
  rw [runSector_ordinary_labels hv]
  unfold historiesValue
  rw [← List.sum_toFinset _ (labelWords_nodup (2 * spec.n))]
  rw [Fintype.card_coe, acceptedWords, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro labels _
  cases he : followLabels spec ⟨0, 0, 0⟩ Key.empty labels with
  | none => simp [labelValue, he]
  | some out => simp [labelValue, terminalOrdinary, he]

/-- Actual lower output sums each accepted word's event total and its single terminal bonus. -/
theorem runSector_eq_sum_accepted {spec : RunSpec} (hv : spec.valid = true) :
    (runSector spec).2 = ∑ word : AcceptedWord spec, (word.eventSum + spec.lowerBonus) := by
  rw [runSector_lower_labels hv]
  unfold historiesValue
  rw [← List.sum_toFinset _ (labelWords_nodup (2 * spec.n))]
  change _ = ∑ word : ↥(acceptedWords spec),
    (((followLabels spec ⟨0, 0, 0⟩ Key.empty word.val).getD (Key.empty, 0)).2 + spec.lowerBonus)
  rw [Finset.sum_coe_sort (acceptedWords spec) (fun labels : List Move =>
    ((followLabels spec ⟨0, 0, 0⟩ Key.empty labels).getD (Key.empty, 0)).2 + spec.lowerBonus)]
  rw [acceptedWords, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro labels _
  cases he : followLabels spec ⟨0, 0, 0⟩ Key.empty labels with
  | none => simp [labelValue, he]
  | some out =>
    simp [labelValue, terminalLower, he]

/-- Both names denote the same prescribed LOW/HIGH terminal bonus. -/
theorem RunSpec.lowerBonus_eq (spec : RunSpec) : spec.lowerBonus = spec.sector.lowerBonus := by
  cases hs : spec.sector <;> simp [RunSpec.lowerBonus, Sector.lowerBonus, hs]

/-- The accepted-word lower sum is the reconstructed source's exact exterior degree. -/
theorem runSector_eq_sum_exterior {spec : RunSpec} (hv : spec.valid = true) :
    (runSector spec).2 =
      ∑ word : AcceptedWord spec, (word.source hv).matchings.2.exteriorArches.card := by
  rw [runSector_eq_sum_accepted hv]
  apply Fintype.sum_congr
  intro word
  obtain ⟨key, a, hf, _⟩ := word.accepted
  rw [word.eventSum_eq hf, spec.lowerBonus_eq]
  exact word.event_exterior hv hf

private theorem sector_fold (specs : List RunSpec) (initial : Counts) :
    specs.foldl (fun total spec =>
      let c := runSector spec
      (total.1 + c.1, total.2 + c.2)) initial =
      (initial.1 + (specs.map (fun spec => (runSector spec).1)).sum,
        initial.2 + (specs.map (fun spec => (runSector spec).2)).sum) := by
  induction specs generalizing initial with
  | nil => simp
  | cons spec specs ih => simp [ih, Nat.add_assoc]

/-- Sequential sector accumulation adds the exact paired outputs. -/
theorem runAtThreshold_pair (n K : ℕ) :
    runAtThreshold n K =
      (((sectorSpecs n K).map (fun spec => (runSector spec).1)).sum,
        ((sectorSpecs n K).map (fun spec => (runSector spec).2)).sum) := by
  simp [runAtThreshold, sector_fold]

/-- The default threshold lies in the specification's permitted range at positive rank. -/
theorem defaultThreshold_valid {n : ℕ} (hn : 0 < n) :
    0 < n / 2 + 1 ∧ n / 2 + 1 ≤ n := by omega

@[simp] theorem evaluate_zero : evaluate 0 = ⟨0, 1, none⟩ := rfl

end Meanders.FirstCrossing
