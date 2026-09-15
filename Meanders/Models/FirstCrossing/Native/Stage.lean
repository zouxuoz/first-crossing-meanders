import Meanders.Models.FirstCrossing.Native.State
import Meanders.Models.FirstCrossing.Original.Schedule

/-! Exact correspondence between native physical progress and the fixed schedule. -/

namespace Meanders.FirstCrossing

/-- The independently specified schedule always has the physical rank's length. -/
theorem RunSpec.schedule_length {s : RunSpec} (hs : s.valid = true) :
    s.schedule.length = 2 * s.n := by
  cases hsector : s.sector with
  | low => simp [RunSpec.schedule, hsector, Sector.schedule]
  | high L u v =>
    have hL : L ≤ 2 * s.n := by
      simp only [RunSpec.valid, hsector, Bool.and_eq_true, decide_eq_true_eq] at hs
      exact hs.2.2.2.1
    simpa only [RunSpec.schedule, hsector] using
      (Sector.schedule_high_length (u := u) (v := v) hL)

/-- A native visit yields exactly the schedule-derived next stage. -/
theorem Stage.ofTick_next (s : RunSpec) (tick : ℕ) {side : Side}
    (hs : s.schedule[tick]? = some side) :
    Stage.ofTick s (tick + 1) = (Stage.ofTick s tick).next side := by
  cases side <;>
    simp [Stage.ofTick, Stage.next, List.take_add_one, hs, List.count_append]

/-- Exact stage validation is preserved by every scheduled physical visit. -/
theorem Stage.valid_next {s : RunSpec} {t : Stage} {side : Side}
    (hs : s.valid = true) (ht : t.valid s = true)
    (hside : s.schedule[t.tick]? = some side) : (t.next side).valid s = true := by
  have hlt : t.tick < s.schedule.length := List.getElem?_eq_some_iff.mp hside |>.1
  rw [s.schedule_length hs] at hlt
  have he : t = Stage.ofTick s t.tick := (of_decide_eq_true ht).2
  have hnext : (t.next side).tick = t.tick + 1 := by cases side <;> rfl
  unfold Stage.valid
  apply decide_eq_true
  refine ⟨by rw [hnext]; omega, ?_⟩
  rw [hnext, Stage.ofTick_next s t.tick hside, ← he]

end Meanders.FirstCrossing
