import Meanders.Models.FirstCrossing.Interpretation.SourceStep
import Meanders.Models.FirstCrossing.Native.Stage

/-! Recover original source words from accepted native labels, without connectivity claims. -/
namespace Meanders.FirstCrossing
open DyckStep

/-- A successful history uses exactly the existing scheduled native successor. -/
inductive NativeHistory (spec : RunSpec) : Stage → Key → List (Side × Move) → Prop
  | nil : NativeHistory spec ⟨0, 0, 0⟩ Key.empty []
  | snoc {t x events side m y} : NativeHistory spec t x events →
      spec.schedule[t.tick]? = some side → rawStep spec t x m = some y →
      NativeHistory spec (t.next side) y (events ++ [(side, m)])

/-- The original letter of an oriented owner, read directly from its move label. -/
def Move.groupLetter (m : Move) : Group → DyckStep
  | .pl | .pr => if m.upperDown then D else U
  | .ql | .qr => if m.lowerDown then D else U

/-- Recover the four original words by selecting visits to each group's side. -/
def historyWord (events : List (Side × Move)) (g : Group) : List DyckStep :=
  events.filterMap fun event => if event.1 = g.side then some (event.2.groupLetter g) else none

theorem historyWord_snoc (events : List (Side × Move)) (side : Side) (m : Move) (g : Group) :
    historyWord (events ++ [(side, m)]) g = historyWord events g ++
      (if side = g.side then [m.groupLetter g] else []) := by
  by_cases h : side = g.side <;> simp [historyWord, List.filterMap_append, h]

/-- Every raw successor exposes its original counter guards and left filter. -/
theorem rawStep_guards {spec : RunSpec} {t : Stage} {x y : Key} {m : Move} {side : Side}
    (hs : spec.schedule[t.tick]? = some side) (h : rawStep spec t x m = some y) :
    countersValid spec (t.next side) y.counters = true ∧
      prefixAllowed spec (t.next side) y.counters = true := by
  obtain ⟨side', hs', hv⟩ := rawStep_valid h
  have he : side' = side := Option.some.inj (hs'.symm.trans hs)
  subst side'
  simp only [validKey, Bool.and_eq_true] at hv
  exact ⟨hv.1.1.1.1.2, hv.1.1.1.2⟩

/-- The recovered word lengths are precisely the original physical progress. -/
theorem NativeHistory.word_length {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (g : Group) :
    (historyWord events g).length = t.processed g.side := by
  induction h with
  | nil => cases g <;> rfl
  | @snoc t x events side m y hist hs hstep ih =>
    rw [historyWord_snoc, List.length_append, ih]
    cases g <;> cases side <;> simp [Group.side, Stage.next, Stage.processed]

/-- Down counters retain the exact multiplicities of recovered original letters. -/
theorem NativeHistory.word_downs {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (g : Group) :
    (historyWord events g).count D = x.counters.get g := by
  induction h with
  | nil => cases g <;> rfl
  | @snoc t x events side m y hist hs hstep ih =>
    obtain ⟨side', hs', hc⟩ := rawStep_counters hstep
    have he : side' = side := Option.some.inj (hs'.symm.trans hs)
    subst side'
    rw [historyWord_snoc, List.count_append, ih, hc]
    cases g <;> cases side <;> cases m <;>
      simp [Move.groupLetter, Move.upperDown, Move.lowerDown, Group.side,
        moveCounters, Group.onSide, Counters.get, Counters.set]

/-- Original nonnegative heights follow from the exact checked counter inequality. -/
theorem NativeHistory.word_height_nonneg {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (g : Group) :
    0 ≤ Dyck.height (historyWord events g) := by
  cases h with
  | nil => rfl
  | @snoc t x events side m y hist hs hstep =>
    have hc := (rawStep_guards hs hstep).1
    have hg := of_decide_eq_true (List.all_eq_true.mp hc g (by cases g <;> simp [Group.all]))
    have hnew := NativeHistory.snoc hist hs hstep
    have hl := hnew.word_length g
    have hd := hnew.word_downs g
    have hcount := count_U_add_count_D (historyWord (events ++ [(side, m)]) g)
    rw [Dyck.height_eq_count]
    omega

private theorem prefix_nonneg_append_letter {w : List DyckStep} {letter : DyckStep}
    (hp : ∀ i, 0 ≤ Dyck.height (w.take i)) (he : 0 ≤ Dyck.height (w ++ [letter])) :
    ∀ i, 0 ≤ Dyck.height ((w ++ [letter]).take i) := by
  intro i
  by_cases hi : i ≤ w.length
  · simpa [List.take_append_of_le_length hi] using hp i
  · rw [List.take_of_length_le (by simp; omega)]
    exact he

/-- Every prefix of each recovered word is a ballot prefix. -/
theorem NativeHistory.word_prefix_nonneg {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (g : Group) :
    ∀ i, 0 ≤ Dyck.height ((historyWord events g).take i) := by
  induction h with
  | nil => intro i; simp [historyWord, Dyck.height]
  | @snoc t x events side m y hist hs hstep ih =>
    have he := (NativeHistory.snoc hist hs hstep).word_height_nonneg g
    rw [historyWord_snoc] at he ⊢
    by_cases hg : side = g.side
    · simp only [hg, ite_true] at he ⊢
      exact prefix_nonneg_append_letter ih he
    · simpa [hg] using ih

/-- Direct original-word chronological filter, including the HIGH endpoint equality. -/
def OriginalPrefix (spec : RunSpec) (i dp dq : ℕ) : Prop :=
  match spec.sector with
  | .low => (i : ℤ) - dp - dq < spec.K
  | .high L _ _ => if i < L then (i : ℤ) - dp - dq < spec.K
      else (i : ℤ) - dp - dq = spec.K

private theorem spec_threshold_pos {spec : RunSpec} (hs : spec.valid = true) : 0 < spec.K := by
  have h := (Bool.and_eq_true_iff.mp hs).1
  have hh := of_decide_eq_true h
  omega

/-- The checked end-prefix filter agrees with its integer source statement. -/
theorem NativeHistory.end_filter {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (hv : spec.valid = true) :
    OriginalPrefix spec t.left
      (downs (historyWord events .pl) t.left) (downs (historyWord events .ql) t.left) := by
  cases h with
  | nil =>
    have hK := spec_threshold_pos hv
    have hz : 0 < spec.n := by
      have hh := of_decide_eq_true ((Bool.and_eq_true_iff.mp hv).1)
      exact hh.1
    cases hsector : spec.sector with
    | low => simp [OriginalPrefix, hsector, downs, historyWord]; omega
    | high L u v =>
      have hL : 0 < L := by
        simp only [RunSpec.valid, hsector, Bool.and_eq_true, decide_eq_true_eq] at hv
        exact hv.2.1
      simp [OriginalPrefix, hsector, hL, downs, historyWord]; omega
  | @snoc t x events side m y hist hs hstep =>
    have hnew := NativeHistory.snoc hist hs hstep
    have hlp := hnew.word_length .pl
    have hlq := hnew.word_length .ql
    have hdp := hnew.word_downs .pl
    have hdq := hnew.word_downs .ql
    simp only [Group.side, Stage.processed, Counters.get] at hlp hlq hdp hdq
    have hdp' : downs (historyWord (events ++ [(side, m)]) .pl) (t.next side).left =
        (historyWord (events ++ [(side, m)]) .pl).count D := by
      unfold downs
      rw [← hlp, List.take_length]
    have hdq' : downs (historyWord (events ++ [(side, m)]) .ql) (t.next side).left =
        (historyWord (events ++ [(side, m)]) .ql).count D := by
      unfold downs
      rw [← hlq, List.take_length]
    rw [hdp', hdq', hdp, hdq]
    obtain ⟨hc, hf⟩ := rawStep_guards hs hstep
    have hp := of_decide_eq_true (List.all_eq_true.mp hc .pl (by simp [Group.all]))
    have hq := of_decide_eq_true (List.all_eq_true.mp hc .ql (by simp [Group.all]))
    simp only [Group.side, Stage.processed, Counters.get] at hp hq
    cases he : spec.sector with
    | low =>
      simp only [prefixAllowed, OriginalPrefix, he, decide_eq_true_eq] at hf ⊢
      omega
    | high L u v =>
      simp only [prefixAllowed, OriginalPrefix, he] at hf ⊢
      split <;> rename_i hL <;> simp only [hL, reduceIte, decide_eq_true_eq] at hf <;> omega

/-- Appending one visit cannot alter previously recovered group prefixes. -/
theorem NativeHistory.downs_snoc_prefix {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (side : Side) (m : Move) (g : Group) {i : ℕ}
    (hi : i ≤ t.processed g.side) :
    downs (historyWord (events ++ [(side, m)]) g) i = downs (historyWord events g) i := by
  rw [historyWord_snoc]
  unfold downs
  rw [List.take_append_of_le_length (by rw [h.word_length]; exact hi)]

/-- The direct left first-hit/LOW filter holds at every original prefix. -/
theorem NativeHistory.left_prefix {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (hv : spec.valid = true) :
    ∀ i, i ≤ t.left → OriginalPrefix spec i
      (downs (historyWord events .pl) i) (downs (historyWord events .ql) i) := by
  induction h with
  | nil =>
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst i
    exact NativeHistory.end_filter NativeHistory.nil hv
  | @snoc t x events side m y hist hs hstep ih =>
    intro i hi
    by_cases hold : i ≤ t.left
    · rw [hist.downs_snoc_prefix side m .pl hold, hist.downs_snoc_prefix side m .ql hold]
      exact ih i hold
    · have hi' : i = (t.next side).left := by cases side <;> simp [Stage.next] at hi ⊢ <;> omega
      rw [hi']
      exact (NativeHistory.snoc hist hs hstep).end_filter hv

theorem NativeHistory.stage_valid {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (hv : spec.valid = true) : t.valid spec = true := by
  induction h with
  | nil => simp [Stage.valid, Stage.ofTick]
  | @snoc t x events side m y hist hs hstep ih => exact Stage.valid_next hv ih hs

theorem RunSpec.schedule_count {spec : RunSpec} (hv : spec.valid = true) (side : Side) :
    spec.schedule.count side = spec.sideLength side := by
  cases hs : spec.sector with
  | low => cases side <;>
      simp [RunSpec.schedule, RunSpec.sideLength, hs, Sector.schedule, List.count_replicate]
  | high L u v =>
    have hL : L ≤ 2 * spec.n := by
      simp only [RunSpec.valid, hs, Bool.and_eq_true, decide_eq_true_eq] at hv
      exact hv.2.2.2.1
    cases side
    · simpa [RunSpec.schedule, RunSpec.sideLength, hs] using
        (Sector.schedule_high_count_left (u := u) (v := v) hL)
    · simpa [RunSpec.schedule, RunSpec.sideLength, hs] using
        (Sector.schedule_high_count_right (u := u) (v := v) hL)

/-- At the final tick every original side has been completely visited. -/
theorem NativeHistory.terminal_progress {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (hv : spec.valid = true) (ht : t.tick = 2 * spec.n)
    (side : Side) : t.processed side = spec.sideLength side := by
  have he := (of_decide_eq_true (h.stage_valid hv)).2
  rw [ht] at he
  rw [he]
  cases side <;>
    simp [Stage.ofTick, Stage.processed, ← spec.schedule_length hv, spec.schedule_count hv]

/-- Positive-rank terminal histories end at an actually validated native key. -/
theorem NativeHistory.terminal_valid {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (hv : spec.valid = true) (ht : t.tick = 2 * spec.n) :
    validKey spec t x = true := by
  cases h with
  | nil =>
    have hn := (of_decide_eq_true (Bool.and_eq_true_iff.mp hv).1).1
    change 0 = 2 * spec.n at ht
    omega
  | @snoc t x events side m y hist hs hstep =>
    obtain ⟨side', hs', hy⟩ := rawStep_valid hstep
    have he := Option.some.inj (hs'.symm.trans hs)
    simpa only [he] using hy

/-- A terminal word has exactly the prescribed down budget, without an extra assumption. -/
theorem NativeHistory.terminal_downs {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (hv : spec.valid = true) (ht : t.tick = 2 * spec.n)
    (g : Group) : (historyWord events g).count D = spec.budgets.get g := by
  have hx := h.terminal_valid hv ht
  simp only [validKey, Bool.and_eq_true] at hx
  have hc := hx.1.1.1.1.2
  have hg := of_decide_eq_true (List.all_eq_true.mp hc g (by cases g <;> simp [Group.all]))
  rw [h.terminal_progress hv ht] at hg
  rw [h.word_downs]
  omega

/-- The final owner height prescribed by one sector. -/
def RunSpec.endHeight (spec : RunSpec) (g : Group) : ℕ :=
  match spec.sector with
  | .low => 0
  | .high _ u v => match g with | .pl | .pr => u | .ql | .qr => v

/-- Valid parity metadata makes each down budget an exact length decomposition. -/
theorem RunSpec.length_budget {spec : RunSpec} (hv : spec.valid = true) (g : Group) :
    spec.sideLength g.side = spec.endHeight g + 2 * spec.budgets.get g := by
  cases hs : spec.sector with
  | low => cases g <;>
      simp [RunSpec.sideLength, RunSpec.endHeight, RunSpec.budgets, Sector.budgets,
        Counters.ofTuple, Counters.get, Group.side, hs]
  | high L u v =>
    have ha : Admissible spec.n spec.K L u v := by
      simp only [RunSpec.valid, hs, Bool.and_eq_true, decide_eq_true_eq] at hv
      exact hv.2.2.2
    unfold Admissible at ha
    cases g <;>
      simp only [RunSpec.sideLength, RunSpec.endHeight, RunSpec.budgets, Sector.budgets,
        Counters.ofTuple, Counters.get, Group.side, hs] <;> omega

/-- Every complete native history reconstructs four independent original ballot halves. -/
def NativeHistory.ballot {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (hv : spec.valid = true) (ht : t.tick = 2 * spec.n)
    (g : Group) : BallotHalf (spec.sideLength g.side) (spec.endHeight g) where
  word := historyWord events g
  length_word := (h.word_length g).trans (h.terminal_progress hv ht g.side)
  height_word := by
    have hl := (h.word_length g).trans (h.terminal_progress hv ht g.side)
    have hd := h.terminal_downs hv ht g
    have he := spec.length_budget hv g
    have hc := count_U_add_count_D (historyWord events g)
    rw [Dyck.height_eq_count]
    omega
  prefix_nonneg := h.word_prefix_nonneg g

/-- Complete native words directly assemble the independently defined source language. -/
def NativeHistory.source {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (hv : spec.valid = true) (ht : t.tick = 2 * spec.n) :
    Source spec := by
  rcases spec with ⟨n, K, sector⟩
  cases sector with
  | low =>
    refine { upper := h.ballot hv ht .pl, lower := h.ballot hv ht .ql, below := ?_ }
    intro i hi
    change i ≤ 2 * n at hi
    have hp := h.terminal_progress hv ht .left
    change t.left = 2 * n at hp
    exact h.left_prefix hv i (by omega)
  | high L u v =>
    have hs : 0 < L ∧ L < 2 * n ∧ Admissible n K L u v := by
      have hh := (Bool.and_eq_true_iff.mp hv).2
      exact of_decide_eq_true hh
    refine {
      cut_le := Nat.le_of_lt hs.2.1
      pl := h.ballot hv ht .pl
      pr := h.ballot hv ht .pr
      ql := h.ballot hv ht .ql
      qr := h.ballot hv ht .qr
      first_hit := ?_ }
    have hp := h.terminal_progress hv ht .left
    change t.left = L at hp
    constructor
    · have hh := h.left_prefix hv L (by omega)
      simpa [OriginalPrefix, NativeHistory.ballot] using hh
    · intro i hi
      have hh := h.left_prefix hv i (by omega)
      simpa [OriginalPrefix, NativeHistory.ballot, hi] using hh

/-- Assembly does not change any of the four recovered original words. -/
theorem NativeHistory.source_word {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (hv : spec.valid = true) (ht : t.tick = 2 * spec.n)
    (g : Group) : (h.source hv ht).word g = historyWord events g := by
  rcases spec with ⟨n, K, sector⟩
  cases sector with
  | low =>
    have hr : historyWord events .pr = [] := List.eq_nil_of_length_eq_zero
      ((h.word_length .pr).trans (h.terminal_progress hv ht .right))
    have hq : historyWord events .qr = [] := List.eq_nil_of_length_eq_zero
      ((h.word_length .qr).trans (h.terminal_progress hv ht .right))
    cases g <;> simp [NativeHistory.source, Source.word, NativeHistory.ballot, hr, hq]
  | high L u v => cases g <;> rfl

/-- The source language carries no information beyond its four original words. -/
theorem Source.eq_of_word {spec : RunSpec} {a b : Source spec}
    (hw : ∀ g, a.word g = b.word g) : a = b := by
  rcases spec with ⟨n, K, sector⟩
  cases sector with
  | low =>
    apply LowSource.ext
    · exact BallotHalf.ext (hw .pl)
    · exact BallotHalf.ext (hw .ql)
  | high L u v =>
    apply HighSource.ext
    · exact BallotHalf.ext (hw .pl)
    · exact BallotHalf.ext (hw .pr)
    · exact BallotHalf.ext (hw .ql)
    · exact BallotHalf.ext (hw .qr)

/-- A terminal accepted label history reconstructs exactly one independent source. -/
theorem NativeHistory.source_unique {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (hv : spec.valid = true) (ht : t.tick = 2 * spec.n) :
    ∃! source : Source spec, ∀ g, source.word g = historyWord events g := by
  refine ⟨h.source hv ht, h.source_word hv ht, ?_⟩
  intro source hs
  apply Source.eq_of_word
  intro g
  exact (hs g).trans (h.source_word hv ht g).symm

theorem historyWord_append (before after : List (Side × Move)) (g : Group) :
    historyWord (before ++ after) g = historyWord before g ++ historyWord after g := by
  simp [historyWord, List.filterMap_append]

/-- The visit at a group's next ordinal has exactly its recorded owner letter. -/
theorem historyWord_visit (before after : List (Side × Move)) (side : Side) (m : Move)
    (g : Group) (hg : side = g.side) :
    (historyWord (before ++ (side, m) :: after) g)[(historyWord before g).length]? =
      some (m.groupLetter g) := by
  have he : before ++ (side, m) :: after = (before ++ [(side, m)]) ++ after := by simp
  rw [he, historyWord_append, historyWord_snoc, ite_eq_left hg, List.append_assoc]
  simp

/-- Every recorded native move is exactly the assembled source's two owner letters. -/
theorem NativeHistory.source_nextMove {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (hv : spec.valid = true) (ht : t.tick = 2 * spec.n)
    {prefixStage : Stage} {prefixKey : Key} {before after : List (Side × Move)}
    (hp : NativeHistory spec prefixStage prefixKey before) {side : Side} {m : Move}
    (he : events = before ++ (side, m) :: after) :
    (h.source hv ht).nextMove prefixStage side = m := by
  have hletter (owner : Bool) :
      ((h.source hv ht).word (Group.onSide owner side))[prefixStage.processed side]? =
        some (m.groupLetter (Group.onSide owner side)) := by
    rw [h.source_word, he]
    have hlen := hp.word_length (Group.onSide owner side)
    have hg : (Group.onSide owner side).side = side := by cases owner <;> cases side <;> rfl
    rw [hg] at hlen
    rw [← hlen]
    exact historyWord_visit before after side m _ hg.symm
  have hu := hletter true
  have hl := hletter false
  cases side <;> cases m <;>
    simp_all [Source.nextMove, Move.groupLetter, Group.onSide, Move.upperDown, Move.lowerDown]

end Meanders.FirstCrossing
