import Meanders.Models.FirstCrossing.Correctness.SourceLabels
import Meanders.Models.FirstCrossing.Interpretation.SourceCoverage
import Meanders.Models.FirstCrossing.Interpretation.SourceCycle

/-!
# Original source interpretation along actual accepted histories

History induction uses the reconstructed source's original letters and the
proved native step preservation. Connected-source totality and terminal
component coverage close the two directions of acceptance.
-/

namespace Meanders.FirstCrossing

/-- Any accepted word carrying a given source's labels reconstructs that exact source. -/
theorem AcceptedWord.source_eq_of_labels {spec : RunSpec} (w : AcceptedWord spec)
    (hv : spec.valid = true) (s : Source spec) (h : w.val = s.scheduledMoves) :
    w.source hv = s := by
  apply Source.scheduledMoves_injective spec
  exact (w.source_labels hv).symm.trans h

/-- Every actual prefix key represents the independently reconstructed full
source at that prefix; successful labels need no connectedness assumption. -/
theorem NativeHistory.source_prefix_represents {spec : RunSpec} {t : Stage} {x : Key}
    {events : List (Side × Move)} (h : NativeHistory spec t x events)
    (hv : spec.valid = true) (ht : t.tick = 2 * spec.n)
    {prefixStage : Stage} {prefixKey : Key} {before : List (Side × Move)}
    (hp : NativeHistory spec prefixStage prefixKey before) {after : List (Side × Move)}
    (he : events = before ++ after) :
    (h.source hv ht).RepresentsKey (hp.source_progress (h.source hv ht)) prefixKey := by
  induction hp generalizing after with
  | nil => exact (h.source hv ht).representsKey_empty
  | @snoc pt px before side m py hp hs hstep ih =>
    have he' : events = before ++ (side, m) :: after := by
      simpa only [List.append_assoc, List.singleton_append] using he
    have hprevious := ih he'
    have hm := h.source_nextMove hv ht hp he'
    rw [← hm] at hstep
    exact hprevious.rawStep ((NativeHistory.snoc hp hs hstep).source_progress (h.source hv ht))
      hs hstep

/-- A successful raw source label supplies exactly the interpreter's next
state and its unchanged original lower event. -/
theorem followLabels_cons_of_raw {spec : RunSpec} {t : Stage} {x y z : Key}
    {side : Side} {m : Move} {labels : List Move} {a : Nat}
    (hs : spec.schedule[t.tick]? = some side) (hraw : rawStep spec t x m = some y)
    (hrest : followLabels spec (t.next side) y labels = some (z, a)) :
    followLabels spec t x (m :: labels) = some (z, lowerIncrement t x m side + a) := by
  simp [followLabels, hs, step, hraw, hrest, Option.bind_eq_bind]

/-- Every nonterminal prefix of a successful complete history keeps a physical
frontier witness for every processed source component. -/
theorem NativeHistory.source_prefix_covered {spec : RunSpec} {t : Stage} {x : Key}
    {events : List (Side × Move)} (h : NativeHistory spec t x events)
    (hv : spec.valid = true) (ht : t.tick = 2 * spec.n) (hn : 0 < spec.n)
    {prefixStage : Stage} {prefixKey : Key} {before : List (Side × Move)}
    (hp : NativeHistory spec prefixStage prefixKey before) {after : List (Side × Move)}
    (he : events = before ++ after) (hbefore : prefixStage.tick < 2 * spec.n) :
    (h.source hv ht).CoveredKey (hp.source_progress (h.source hv ht)) prefixKey hn := by
  induction hp generalizing after with
  | nil => exact (h.source hv ht).coveredKey_initial hn
  | @snoc pt px before side m py hp hs hstep ih =>
    have he' : events = before ++ (side, m) :: after := by
      simpa only [List.append_assoc, List.singleton_append] using he
    have hprevTick : pt.tick < 2 * spec.n := by
      cases side <;> simp only [Stage.next] at hbefore <;> omega
    have hprevious := ih he' hprevTick
    have hrep := h.source_prefix_represents hv ht hp he'
    have hm := h.source_nextMove hv ht hp he'
    rw [← hm] at hstep
    exact hprevious.rawStep hrep
      ((NativeHistory.snoc hp hs hstep).source_progress (h.source hv ht)) hs hbefore hstep

/-- Every positive-rank full successful native history reconstructs a connected
original source. The final cycle conclusion uses processed-component coverage. -/
theorem NativeHistory.source_connected {spec : RunSpec} {t : Stage} {x : Key}
    {events : List (Side × Move)} (h : NativeHistory spec t x events)
    (hv : spec.valid = true) (ht : t.tick = 2 * spec.n) :
    (unionGraph (h.source hv ht).matchings).Connected := by
  have hn : 0 < spec.n := (of_decide_eq_true (Bool.and_eq_true_iff.mp hv).1).1
  cases h with
  | nil => simp only at ht; omega
  | @snoc pt px before side m py hp hs hstep =>
    let full := NativeHistory.snoc hp hs hstep
    have hprevTick : pt.tick < 2 * spec.n := by
      cases side <;> simp only [Stage.next] at ht <;> omega
    have he : before ++ [(side, m)] = before ++ (side, m) :: [] := rfl
    have hcovered := full.source_prefix_covered hv ht hn hp he hprevTick
    have hrep := full.source_prefix_represents hv ht hp he
    have hm := full.source_nextMove hv ht hp he
    have hraw := hstep
    rw [← hm] at hraw
    exact hcovered.rawStep_terminal_connected hrep
      (full.source_progress (full.source hv ht)) hs ht hraw

/-- An accepted evaluator word reconstructs a connected original source. -/
theorem AcceptedWord.source_connected {spec : RunSpec} (w : AcceptedWord spec)
    (hv : spec.valid = true) : (unionGraph (w.source hv).matchings).Connected := by
  obtain ⟨key, a, hf, _⟩ := w.accepted
  obtain ⟨t, events, hh, hm, ht⟩ := followLabels_history NativeHistory.nil hf
  simp only [List.nil_append, Nat.zero_add] at hh ht
  rw [w.length] at ht
  have he : w.source hv = hh.source hv ht := by
    apply Source.scheduledMoves_injective spec
    exact (w.source_labels hv).symm.trans (hm.symm.trans (hh.source_labels hv ht))
  rw [he]
  exact hh.source_connected hv ht

/-- Local native totality along the original labels extends to the exact finite
interpreter, retaining source interpretation and native validity at every tick. -/
theorem Source.followLabels_of_local_total {spec : RunSpec} (s : Source spec)
    (hlocal : ∀ (tick : Nat) (_ : tick < 2 * spec.n) (key : Key),
      s.RepresentsKey (s.ofTick_progress tick) key →
      validKey spec (Stage.ofTick spec tick) key = true →
      ∃ next, rawStep spec (Stage.ofTick spec tick) key (s.scheduledMove tick) = some next)
    (count tick : Nat) (hbound : tick + count ≤ 2 * spec.n)
    (key : Key) (hrep : s.RepresentsKey (s.ofTick_progress tick) key)
    (hvalid : validKey spec (Stage.ofTick spec tick) key = true) :
    ∃ last a, followLabels spec (Stage.ofTick spec tick) key
      ((List.range' tick count).map s.scheduledMove) = some (last, a) ∧
      s.RepresentsKey (s.ofTick_progress (tick + count)) last ∧
      validKey spec (Stage.ofTick spec (tick + count)) last = true := by
  induction count generalizing tick key with
  | zero => exact ⟨key, 0, rfl, hrep, hvalid⟩
  | succ count ih =>
    have hi : tick < spec.schedule.length := by rw [s.schedule_length]; omega
    let side := spec.schedule[tick]
    have hs : spec.schedule[tick]? = some side := List.getElem?_eq_getElem hi
    obtain ⟨next, hraw⟩ := hlocal tick (by omega) key hrep hvalid
    have hm : s.scheduledMove tick = s.nextMove (Stage.ofTick spec tick) side := by
      simp only [Source.scheduledMove, hs]
    have hraw' := hraw
    rw [hm] at hraw'
    have hprogress : s.Progress ((Stage.ofTick spec tick).next side) := by
      rw [← Stage.ofTick_next spec tick hs]
      exact s.ofTick_progress _
    have hnextRep := hrep.rawStep hprogress hs hraw'
    have hnextValid : validKey spec ((Stage.ofTick spec tick).next side) next = true := by
      obtain ⟨side', hs', hv⟩ := rawStep_valid hraw
      have he : side' = side := Option.some.inj (hs'.symm.trans hs)
      subst side'
      exact hv
    have hnextRep' : s.RepresentsKey (s.ofTick_progress (tick + 1)) next := by
      simpa only [Stage.ofTick_next spec tick hs] using hnextRep
    rw [← Stage.ofTick_next spec tick hs] at hnextValid
    obtain ⟨last, a, hfollow, hlast, hvlast⟩ :=
      ih (tick + 1) (by omega) next hnextRep' hnextValid
    have hfollow' := hfollow
    rw [Stage.ofTick_next spec tick hs] at hfollow'
    refine ⟨last, lowerIncrement (Stage.ofTick spec tick) key (s.scheduledMove tick) side + a,
      ?_, ?_, ?_⟩
    · rw [List.range'_succ, List.map_cons]
      exact followLabels_cons_of_raw hs hraw hfollow'
    · simpa only [Nat.add_assoc, Nat.add_comm 1 count] using hlast
    · simpa only [Nat.add_assoc, Nat.add_comm 1 count] using hvlast

/-- Every connected original source completes the actual finite native
interpreter, with its canonical terminal key accepted by all terminal checks. -/
theorem Source.followLabels_complete {spec : RunSpec} (s : Source spec)
    (hv : spec.valid = true) (hconn : (unionGraph s.matchings).Connected) :
    ∃ key a, followLabels spec ⟨0, 0, 0⟩ Key.empty s.scheduledMoves = some (key, a) ∧
      terminalKey spec key = true := by
  have hlocal : ∀ (tick : Nat) (_ : tick < 2 * spec.n) (key : Key),
      s.RepresentsKey (s.ofTick_progress tick) key →
      validKey spec (Stage.ofTick spec tick) key = true →
      ∃ next, rawStep spec (Stage.ofTick spec tick) key (s.scheduledMove tick) = some next := by
    intro tick ht key hrep hvalid
    have hi : tick < spec.schedule.length := by rw [s.schedule_length]; exact ht
    let side := spec.schedule[tick]
    have hs : spec.schedule[tick]? = some side := List.getElem?_eq_getElem hi
    have hnext : s.Progress ((Stage.ofTick spec tick).next side) := by
      rw [← Stage.ofTick_next spec tick hs]
      exact s.ofTick_progress _
    obtain ⟨next, hraw, _⟩ := hrep.nextMove_total hvalid hnext hs hconn
    exact ⟨next, by simpa only [Source.scheduledMove, hs] using hraw⟩
  obtain ⟨key, a, hfollow, hrep, hvalid⟩ := s.followLabels_of_local_total hlocal
    (2 * spec.n) 0 (by omega) Key.empty s.representsKey_empty (initial_validKey spec hv)
  refine ⟨key, a, ?_, ?_⟩
  · simpa only [← List.range_eq_range', Source.scheduledMoves,
      show Stage.ofTick spec 0 = ⟨0, 0, 0⟩ from rfl] using hfollow
  · have hterminal := Source.RepresentsKey.terminal (s := s) (key := key)
      (by simpa only [Nat.zero_add] using hrep)
    simp only [terminalKey, Nat.zero_add] at hvalid ⊢
    rw [hvalid, decide_eq_true hterminal]
    rfl

/-- The exact scheduled word of every connected source is in the evaluator's
finite accepted set; no alternative evaluator or source enumeration is run. -/
theorem Source.scheduledMoves_mem_accepted {spec : RunSpec} (s : Source spec)
    (hv : spec.valid = true) (hconn : (unionGraph s.matchings).Connected) :
    s.scheduledMoves ∈ acceptedWords spec := by
  obtain ⟨key, a, hfollow, hterminal⟩ := s.followLabels_complete hv hconn
  apply Finset.mem_filter.mpr
  refine ⟨List.mem_toFinset.mpr (mem_labelWords.mpr s.scheduledMoves_length), ?_⟩
  simp only [hfollow, Option.any_some, hterminal]

/-- Accepted actual native label words are in explicit bijection with the
connected independent original source language in the same oriented sector. -/
noncomputable def acceptedSourceEquiv (spec : RunSpec) (hv : spec.valid = true) :
    AcceptedWord spec ≃ {s : Source spec // (unionGraph s.matchings).Connected} :=
  Equiv.ofBijective (fun w => ⟨w.source hv, w.source_connected hv⟩) (by
    constructor
    · intro a b he
      exact AcceptedWord.source_injective hv (congrArg Subtype.val he)
    · intro source
      let word : AcceptedWord spec :=
        ⟨source.val.scheduledMoves, source.val.scheduledMoves_mem_accepted hv source.property⟩
      refine ⟨word, Subtype.ext ?_⟩
      exact word.source_eq_of_labels hv source.val rfl)

/-- The bijection preserves the original source, hence every original diagram weight. -/
@[simp] theorem acceptedSourceEquiv_source (spec : RunSpec) (hv : spec.valid = true)
    (w : AcceptedWord spec) : (acceptedSourceEquiv spec hv w).val = w.source hv := rfl

end Meanders.FirstCrossing
