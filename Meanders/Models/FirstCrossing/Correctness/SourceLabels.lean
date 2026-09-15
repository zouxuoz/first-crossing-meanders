import Meanders.Models.FirstCrossing.Correctness.Accepted
import Meanders.Models.FirstCrossing.Interpretation.Preservation

/-!
# The complete scheduled label word uniquely determines its original source

This is a direct word-level result. It does not require a successful native run
or any source connectivity hypothesis.
-/

namespace Meanders.FirstCrossing

@[simp] theorem Source.scheduledMoves_length {spec : RunSpec} (s : Source spec) :
    s.scheduledMoves.length = 2 * spec.n := by simp [Source.scheduledMoves]

/-- Every genuine tick reads its original fixed scheduled label. -/
theorem Source.scheduledMoves_get {spec : RunSpec} (s : Source spec) {tick : Nat}
    (ht : tick < 2 * spec.n) : s.scheduledMoves[tick]? = some (s.scheduledMove tick) := by
  simp [Source.scheduledMoves, List.getElem?_range ht]

/-- A source label contains exactly each visited group's original next letter. -/
theorem Source.nextMove_groupLetter {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side)) (g : Group)
    (hg : g.side = side) :
    (s.word g)[t.processed side]? = some ((s.nextMove t side).groupLetter g) := by
  have h := s.nextMove_letters hnext
  cases side <;> cases g <;>
    simp only [Group.side, reduceCtorEq] at hg <;> try contradiction
  all_goals simpa only [Move.groupLetter, Group.onSide, ite_true, Bool.false_eq_true, ite_false]
    using (by first | exact h.1 | exact h.2)

/-- Equal scheduled labels give equal original word prefixes after every tick. -/
theorem Source.prefix_eq_of_scheduledMoves {spec : RunSpec} (s r : Source spec)
    (he : s.scheduledMoves = r.scheduledMoves) (tick : Nat) (ht : tick ≤ 2 * spec.n) :
    ∀ g, (s.word g).take ((Stage.ofTick spec tick).processed g.side) =
      (r.word g).take ((Stage.ofTick spec tick).processed g.side) := by
  induction tick with
  | zero => intro g; cases g <;> rfl
  | succ tick ih =>
    have hlt : tick < spec.schedule.length := by rw [s.schedule_length]; omega
    let side := spec.schedule[tick]
    have hside : spec.schedule[tick]? = some side := List.getElem?_eq_getElem hlt
    have hm : s.nextMove (Stage.ofTick spec tick) side =
        r.nextMove (Stage.ofTick spec tick) side := by
      have hh := congrArg (fun ws => ws[tick]?) he
      rw [s.scheduledMoves_get (by omega), r.scheduledMoves_get (by omega)] at hh
      simpa only [Source.scheduledMove, hside] using Option.some.inj hh
    have hs : s.Progress ((Stage.ofTick spec tick).next side) := by
      rw [← Stage.ofTick_next spec tick hside]
      exact s.ofTick_progress _
    have hr : r.Progress ((Stage.ofTick spec tick).next side) := by
      rw [← Stage.ofTick_next spec tick hside]
      exact r.ofTick_progress _
    intro g
    rw [Stage.ofTick_next spec tick hside, Stage.processed_next]
    by_cases hg : side = g.side
    · rw [ite_eq_left hg, List.take_add_one, List.take_add_one, ih (by omega) g]
      have hletters := (s.nextMove_groupLetter hs g hg.symm).trans
        ((congrArg (fun m => some (m.groupLetter g)) hm).trans
          (r.nextMove_groupLetter hr g hg.symm).symm)
      rw [hg] at hletters
      rw [hletters]
    · rw [ite_eq_right hg, Nat.add_zero]
      exact ih (by omega) g

/-- The fixed schedule loses neither owner letters nor their original chronology. -/
theorem Source.scheduledMoves_injective (spec : RunSpec) :
    Function.Injective (fun s : Source spec => s.scheduledMoves) := by
  intro s r he
  apply Source.eq_of_word
  intro g
  have hp := s.prefix_eq_of_scheduledMoves r he (2 * spec.n) le_rfl g
  rw [s.ofTick_end_processed, List.take_of_length_le (s.word_length g).le,
    List.take_of_length_le (r.word_length g).le] at hp
  exact hp

end Meanders.FirstCrossing
