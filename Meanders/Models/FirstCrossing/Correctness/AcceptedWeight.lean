import Meanders.Models.FirstCrossing.Correctness.Accepted
namespace Meanders.FirstCrossing

/-- A contiguous suffix of the source's fixed scheduled labels. -/
def Source.movesFrom {spec : RunSpec} (source : Source spec) (tick k : ℕ) : List Move :=
  (List.range k).map (fun i => source.scheduledMove (tick + i))

theorem Source.movesFrom_succ {spec : RunSpec} (source : Source spec) (tick k : ℕ) :
    source.movesFrom tick (k + 1) = source.scheduledMove tick :: source.movesFrom (tick + 1) k := by
  simp [Source.movesFrom, List.range_succ_eq_map, List.map_map, Function.comp_def,
    Nat.add_comm, Nat.add_left_comm]

/-- The observer returned by the paired step is its actual original-key increment. -/
theorem step_increment {spec : RunSpec} {t : Stage} {key next : Key}
    {m : Move} {side : Side} {a : ℕ}
    (hs : spec.schedule[t.tick]? = some side) (he : step spec t key m = some (next, a)) :
    a = lowerIncrement t key m side := by
  have hr := step_raw he
  have hh := congrArg (fun out => out.map Prod.snd) he
  simpa [step, hs, hr] using hh.symm

/-- Actual source-labelled execution telescopes its returned event weight. -/
theorem followLabels_returns {spec : RunSpec} (source : Source spec) (k tick : ℕ)
    (hb : tick + k ≤ 2 * spec.n) {key out : Key} {a : ℕ}
    (hk : key.counters = source.counters (Stage.ofTick spec tick))
    (hf : followLabels spec (Stage.ofTick spec tick) key (source.movesFrom tick k) =
      some (out, a)) :
    a + source.lowerReturns (Stage.ofTick spec tick) =
      source.lowerReturns (Stage.ofTick spec (tick + k)) := by
  induction k generalizing tick key out a with
  | zero =>
    have ha : a = 0 := by
      simpa [Source.movesFrom, followLabels] using
        (congrArg (fun result => result.map Prod.snd) hf).symm
    simp [ha]
  | succ k ih =>
    have hitick : tick < spec.schedule.length := by rw [source.schedule_length]; omega
    obtain ⟨side, hs⟩ : ∃ side, spec.schedule[tick]? = some side :=
      ⟨spec.schedule[tick], List.getElem?_eq_getElem hitick⟩
    have hstage : (Stage.ofTick spec tick).tick = tick := rfl
    have hs' : spec.schedule[(Stage.ofTick spec tick).tick]? = some side := hs
    have hmove : source.scheduledMove tick = source.nextMove (Stage.ofTick spec tick) side := by
      simp [Source.scheduledMove, hs]
    rw [source.movesFrom_succ, hmove] at hf
    cases he : step spec (Stage.ofTick spec tick) key
        (source.nextMove (Stage.ofTick spec tick) side) with
    | none => simp [followLabels, hs', he] at hf
    | some pair =>
      rcases pair with ⟨next, b⟩
      have hc : next.counters = source.counters ((Stage.ofTick spec tick).next side) := by
        obtain ⟨side', hs'', hc⟩ := rawStep_counters (step_raw he)
        have hside : side' = side := Option.some.inj (hs''.symm.trans hs')
        rw [hside, hk, source.nextMove_counters] at hc
        exact hc
      have hb' := step_increment hs' he
      have hr := source.lowerReturns_next (source.ofTick_progress tick) side key hk
      rw [← hb'] at hr
      have ht : Stage.ofTick spec (tick + 1) = (Stage.ofTick spec tick).next side :=
        Stage.ofTick_next spec tick hs
      cases htail : followLabels spec ((Stage.ofTick spec tick).next side) next
          (source.movesFrom (tick + 1) k) with
      | none => simp [followLabels, hs', he, htail] at hf
      | some pair =>
        rcases pair with ⟨last, c⟩
        have ha : b + c = a := by
          simpa [followLabels, hs', he, htail, Option.bind_eq_bind] using
            congrArg (fun result => result.map Prod.snd) hf
        have hc' : next.counters = source.counters (Stage.ofTick spec (tick + 1)) := by
          simpa only [ht] using hc
        have htail' : followLabels spec (Stage.ofTick spec (tick + 1)) next
            (source.movesFrom (tick + 1) k) = some (last, c) := by simpa only [ht] using htail
        have hend := ih (tick + 1) (by omega) hc' htail'
        rw [ht] at hend
        have heq : tick + 1 + k = tick + (k + 1) := by omega
        rw [heq] at hend
        omega

/-- A complete accepted source label word has exactly its scheduled lower event sum. -/
theorem followLabels_scheduledLower {spec : RunSpec} (source : Source spec) {key : Key} {a : ℕ}
    (hf : followLabels spec ⟨0, 0, 0⟩ Key.empty source.scheduledMoves = some (key, a)) :
    a = ∑ i ∈ Finset.range (2 * spec.n), source.scheduledLowerIncrement i := by
  have hk : Key.empty.counters = source.counters (Stage.ofTick spec 0) := by
    simp [Key.empty, Source.counters, Counters.ofFn, Counters.zero, Stage.ofTick,
      Stage.processed, Group.side, downs]
  have hlabels : source.movesFrom 0 (2 * spec.n) = source.scheduledMoves := by
    simp [Source.movesFrom, Source.scheduledMoves]
  have hh := followLabels_returns source (2 * spec.n) 0 (by omega) hk
    (by simpa [hlabels, Stage.ofTick] using hf)
  rw [source.scheduledLower_sum le_rfl]
  simpa [Source.lowerReturns, Stage.ofTick, returnPrefix] using hh

/-- The accepted word's accumulated observer is the reconstructed source's exact sum. -/
theorem AcceptedWord.event_eq_scheduled {spec : RunSpec} (word : AcceptedWord spec)
    (hv : spec.valid = true) {key : Key} {a : ℕ}
    (hf : followLabels spec ⟨0, 0, 0⟩ Key.empty word.val = some (key, a)) :
    a = ∑ i ∈ Finset.range (2 * spec.n), (word.source hv).scheduledLowerIncrement i := by
  rw [word.source_labels hv] at hf
  exact followLabels_scheduledLower (word.source hv) hf

/-- Adding the single prescribed bonus gives the source's lower exterior degree. -/
theorem AcceptedWord.event_exterior {spec : RunSpec} (word : AcceptedWord spec)
    (hv : spec.valid = true) {key : Key} {a : ℕ}
    (hf : followLabels spec ⟨0, 0, 0⟩ Key.empty word.val = some (key, a)) :
    a + spec.sector.lowerBonus = (word.source hv).matchings.2.exteriorArches.card := by
  rw [word.event_eq_scheduled hv hf]
  exact (word.source hv).scheduledLower_exterior

end Meanders.FirstCrossing
