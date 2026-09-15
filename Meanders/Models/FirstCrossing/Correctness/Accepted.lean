import Meanders.Models.FirstCrossing.Interpretation.Observer
import Meanders.Models.FirstCrossing.Interpretation.Histories
import Meanders.Models.FirstCrossing.Correctness.JointLayer

/-! Interface between the actual finite-label evaluator and reconstructed source histories. -/
namespace Meanders.FirstCrossing

/-- Every prefix history lies within both original side lengths. -/
theorem NativeHistory.progress_bound {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (side : Side) :
    t.processed side ≤ spec.sideLength side := by
  cases h with
  | nil => cases side <;> simp [Stage.processed]
  | @snoc t x events visit m y hist hs hstep =>
    have hc := (rawStep_guards hs hstep).1
    cases side
    · exact (of_decide_eq_true (List.all_eq_true.mp hc .pl (by simp [Group.all]))).1
    · exact (of_decide_eq_true (List.all_eq_true.mp hc .pr (by simp [Group.all]))).1

/-- The native prefix has valid source progress for any source in the same sector. -/
theorem NativeHistory.source_progress {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (source : Source spec) : source.Progress t := by
  have hl := h.progress_bound .left
  have hr := h.progress_bound .right
  cases hs : spec.sector <;>
    simp_all [Source.Progress, Source.cut, RunSpec.sideLength, Stage.processed]

/-- Attaching the lower event does not change the accepted raw successor. -/
theorem step_raw {spec : RunSpec} {t : Stage} {x y : Key} {m : Move} {a : ℕ}
    (h : step spec t x m = some (y, a)) : rawStep spec t x m = some y := by
  cases hs : spec.schedule[t.tick]? with
  | none => simp [step, hs] at h
  | some side =>
    cases hr : rawStep spec t x m with
    | none => simp [step, hs, hr] at h
    | some key =>
      have hk : key = y := by
        simpa [step, hs, hr] using congrArg (fun out => out.map Prod.fst) h
      simp [hk]

/-- Every accepted evaluator word extends the original native history exactly. -/
theorem followLabels_history {spec : RunSpec} {t : Stage} {x y : Key} {events : List (Side × Move)}
    (h : NativeHistory spec t x events) {labels : List Move} {a : ℕ}
    (hf : followLabels spec t x labels = some (y, a)) :
    ∃ finalStage suffix, NativeHistory spec finalStage y (events ++ suffix) ∧
      suffix.map Prod.snd = labels ∧ finalStage.tick = t.tick + labels.length := by
  induction labels generalizing t x events y a with
  | nil =>
    have he : x = y := by simpa [followLabels] using congrArg (fun out => out.map Prod.fst) hf
    subst y
    exact ⟨t, [], by simpa using h, rfl, by simp⟩
  | cons m ms ih =>
    cases hs : spec.schedule[t.tick]? with
    | none => simp [followLabels, hs] at hf
    | some side =>
      cases he : step spec t x m with
      | none => simp [followLabels, hs, he] at hf
      | some out =>
        rcases out with ⟨next, b⟩
        cases hh : followLabels spec (t.next side) next ms with
        | none => simp [followLabels, hs, he, hh] at hf
        | some last =>
          rcases last with ⟨last, c⟩
          have hlast : last = y := by
            simpa [followLabels, hs, he, hh, Option.bind_eq_bind] using
              congrArg (fun out => out.map Prod.fst) hf
          subst last
          obtain ⟨finalStage, suffix, hhist, hmoves, htick⟩ :=
            ih (NativeHistory.snoc h hs (step_raw he)) hh
          refine ⟨finalStage, (side, m) :: suffix, ?_, ?_, ?_⟩
          · simpa [List.append_assoc] using hhist
          · simp [hmoves]
          · cases side <;> simp only [Stage.next] at htick <;>
              simp only [List.length_cons] <;> omega

end Meanders.FirstCrossing

/-! Accepted native label words and their injective reconstruction into the independent source. -/
namespace Meanders.FirstCrossing

/-- Original two-owner label at one fixed scheduled physical tick. -/
def Source.scheduledMove {spec : RunSpec} (source : Source spec) (tick : ℕ) : Move :=
  match spec.schedule[tick]? with
  | none => .UU
  | some side => source.nextMove (Stage.ofTick spec tick) side

/-- The entire original label word in the fixed sector schedule. -/
def Source.scheduledMoves {spec : RunSpec} (source : Source spec) : List Move :=
  (List.range (2 * spec.n)).map source.scheduledMove

/-- Every prefix's labels equal the reconstructed source's fixed scheduled labels. -/
theorem NativeHistory.source_prefix_labels {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (hv : spec.valid = true) (ht : t.tick = 2 * spec.n)
    {prefixStage : Stage} {prefixKey : Key} {before : List (Side × Move)}
    (hp : NativeHistory spec prefixStage prefixKey before) {after : List (Side × Move)}
    (he : events = before ++ after) :
    before.map Prod.snd = (List.range prefixStage.tick).map (h.source hv ht).scheduledMove := by
  induction hp generalizing after with
  | nil => simp
  | @snoc pt px before side m py hp hs hstep ih =>
    have he' : events = before ++ (side, m) :: after := by simpa [List.append_assoc] using he
    have hi := ih he'
    have hmove := h.source_nextMove hv ht hp he'
    have hstage : Stage.ofTick spec pt.tick = pt :=
      (of_decide_eq_true (hp.stage_valid hv)).2.symm
    have hscheduled : (h.source hv ht).scheduledMove pt.tick = m := by
      simpa only [Source.scheduledMove, hs, hstage] using hmove
    have hnext : (pt.next side).tick = pt.tick + 1 := by cases side <;> rfl
    rw [List.map_append, hi, hnext, List.range_succ, List.map_append]
    simp [hscheduled]

/-- A completed history has exactly the source's complete scheduled label word. -/
theorem NativeHistory.source_labels {spec : RunSpec} {t : Stage} {x : Key} {events}
    (h : NativeHistory spec t x events) (hv : spec.valid = true) (ht : t.tick = 2 * spec.n) :
    events.map Prod.snd = (h.source hv ht).scheduledMoves := by
  have he := h.source_prefix_labels hv ht h (after := []) (by simp)
  simpa only [ht, Source.scheduledMoves] using he

/-- Finite accepted words are determined by the actual interpreter and terminal key filter. -/
def acceptedWords (spec : RunSpec) : Finset (List Move) :=
  ((labelWords (2 * spec.n)).toFinset).filter fun labels =>
    (followLabels spec ⟨0, 0, 0⟩ Key.empty labels).any (fun out => terminalKey spec out.1)

/-- An accepted all-four-label word; coincident state targets do not identify words. -/
abbrev AcceptedWord (spec : RunSpec) := ↥(acceptedWords spec)

theorem AcceptedWord.length {spec : RunSpec} (word : AcceptedWord spec) :
    word.val.length = 2 * spec.n := by
  have h := (Finset.mem_filter.mp word.property).1
  exact mem_labelWords.mp (List.mem_toFinset.mp h)

/-- Acceptance supplies both the exact terminal output and the terminal filter. -/
theorem AcceptedWord.accepted {spec : RunSpec} (word : AcceptedWord spec) :
    ∃ key a, followLabels spec ⟨0, 0, 0⟩ Key.empty word.val = some (key, a) ∧
      terminalKey spec key = true := by
  have h := (Finset.mem_filter.mp word.property).2
  cases he : followLabels spec ⟨0, 0, 0⟩ Key.empty word.val with
  | none => simp [he] at h
  | some out => exact ⟨out.1, out.2, rfl, by simpa [he] using h⟩

/-- Actual acceptance reconstructs an independently defined source with the same labels. -/
theorem AcceptedWord.source_exists {spec : RunSpec} (word : AcceptedWord spec)
    (hv : spec.valid = true) : ∃ source : Source spec, word.val = source.scheduledMoves := by
  obtain ⟨key, a, hf, _⟩ := word.accepted
  obtain ⟨t, events, hh, hm, ht⟩ := followLabels_history NativeHistory.nil hf
  simp only [List.nil_append, Nat.zero_add] at hh ht
  rw [word.length] at ht
  exact ⟨hh.source hv ht, hm.symm.trans (hh.source_labels hv ht)⟩

/-- Source reconstruction of an accepted word; its existence uses original guards only. -/
noncomputable def AcceptedWord.source {spec : RunSpec} (word : AcceptedWord spec)
    (hv : spec.valid = true) : Source spec := Classical.choose (word.source_exists hv)

theorem AcceptedWord.source_labels {spec : RunSpec} (word : AcceptedWord spec)
    (hv : spec.valid = true) : word.val = (word.source hv).scheduledMoves :=
  Classical.choose_spec (word.source_exists hv)

/-- Distinct accepted labels remain distinct after reconstruction, even when keys collide. -/
theorem AcceptedWord.source_injective {spec : RunSpec} (hv : spec.valid = true) :
    Function.Injective (fun word : AcceptedWord spec => word.source hv) := by
  intro a b he
  change a.source hv = b.source hv at he
  apply Subtype.ext
  rw [a.source_labels hv, b.source_labels hv, he]

end Meanders.FirstCrossing
