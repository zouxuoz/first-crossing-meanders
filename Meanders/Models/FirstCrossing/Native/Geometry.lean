import Meanders.Models.FirstCrossing.Native.Transition

/-! Counter arithmetic used by native FIFO promotion. -/

namespace Meanders.FirstCrossing

/-- Emission uses the original down counter, irrespective of previous contractions. -/
theorem emitted_eq_originalCounters (s : RunSpec) (t : Stage) (c : Counters)
    (g : Group) {L u v : ℕ} (hs : s.sector = .high L u v)
    (hc : c.get g ≤ s.budgets.get g) :
    (geometry s t c).emitted.get g =
      t.processed g.side - s.budgets.get g - c.get g := by
  simp only [geometry, hs, Counters.get_ofFn]
  omega

/-- The reservoir is exactly the part that might still close in a feasible suffix. -/
theorem reservoir_eq_min (s : RunSpec) (t : Stage) (c : Counters)
    (g : Group) {L u v : ℕ} (hs : s.sector = .high L u v) :
    (geometry s t c).reservoir.get g =
      min (t.processed g.side - 2 * c.get g) (s.budgets.get g - c.get g) := by
  simp only [geometry, hs, Counters.get_ofFn]
  omega

/-- A visit advances original progress on exactly its physical side. -/
theorem Stage.processed_next (t : Stage) (side observed : Side) :
    (t.next side).processed observed = t.processed observed + if side = observed then 1 else 0 := by
  cases side <;> cases observed <;> rfl

/-- A labelled visit advances the selected owner's original counter by zero or one. -/
theorem moveCounters_between (c : Counters) (side : Side) (m : Move) (g : Group) :
    c.get g ≤ (moveCounters c side m).get g ∧
      (moveCounters c side m).get g ≤ c.get g + if side = g.side then 1 else 0 := by
  cases side <;> cases m <;> cases g <;>
    simp [moveCounters, Group.onSide, Group.side, Counters.get, Counters.set,
      Move.upperDown, Move.lowerDown]

/-- Every owner emits at most one new ordinal per physical vertex and never un-emits one. -/
theorem emitted_next_between (s : RunSpec) (t : Stage) (c : Counters)
    (side : Side) (m : Move) (g : Group)
    (hbudget : c.get g ≤ s.budgets.get g)
    (hbudgetNew : (moveCounters c side m).get g ≤ s.budgets.get g) :
    (geometry s t c).emitted.get g ≤
        (geometry s (t.next side) (moveCounters c side m)).emitted.get g ∧
      (geometry s (t.next side) (moveCounters c side m)).emitted.get g ≤
        (geometry s t c).emitted.get g + if side = g.side then 1 else 0 := by
  cases hs : s.sector with
  | low => simp [geometry, hs, Counters.zero, Counters.get]
  | high L u v =>
    rw [emitted_eq_originalCounters s t c g hs hbudget,
      emitted_eq_originalCounters s (t.next side) (moveCounters c side m) g hs hbudgetNew]
    have hc := moveCounters_between c side m g
    rw [Stage.processed_next]
    split_ifs at hc ⊢ <;> omega

/-- Each prescribed per-owner drain is empty or consists of one FIFO join.
This is a property of the unchanged original-counter recurrence, not a new guard. -/
theorem joined_next_between (s : RunSpec) (t : Stage) (c : Counters)
    (side : Side) (m : Move) (g : Group)
    (hbudget : ∀ group, c.get group ≤ s.budgets.get group)
    (hbudgetNew : ∀ group, (moveCounters c side m).get group ≤ s.budgets.get group) :
    let old := (geometry s t c).emitted
    let new := (geometry s (t.next side) (moveCounters c side m)).emitted
    min (old.get g) (old.get g.other) ≤ min (new.get g) (new.get g.other) ∧
      min (new.get g) (new.get g.other) - min (old.get g) (old.get g.other) ≤ 1 := by
  dsimp only
  have h := emitted_next_between s t c side m g (hbudget g) (hbudgetNew g)
  have ho := emitted_next_between s t c side m g.other
    (hbudget g.other) (hbudgetNew g.other)
  split_ifs at h ho <;> omega

end Meanders.FirstCrossing

/-!
# Native retained-length conservation through one physical visit

Each retained group is its original active height minus its owner's completed
FIFO joins. Original counter changes and monotone emitted prefixes therefore
account exactly for every physical endpoint edit and subsequent FIFO removal.
No target group length or successful candidate validation is assumed.
-/

namespace Meanders.FirstCrossing

/-- Retained endpoints and completed joins exhaust the original active height. -/
theorem geometry_length_add_joined (s : RunSpec) (t : Stage) (c : Counters) (g : Group) :
    (geometry s t c).length.get g +
        min ((geometry s t c).emitted.get g) ((geometry s t c).emitted.get g.other) =
      (geometry s t c).height.get g := by
  cases hs : s.sector with
  | low => cases g <;> simp [geometry, hs, Counters.zero, Counters.get]
  | high L u v =>
    simp only [geometry, hs, Counters.get_ofFn]
    omega

/-- Original heights change by the visit indicator minus twice the new down count. -/
theorem geometry_height_next_conservation (s : RunSpec) (t : Stage) (c : Counters)
    (side : Side) (m : Move) (g : Group)
    (hheight : 2 * c.get g ≤ t.processed g.side)
    (hheightNew : 2 * (moveCounters c side m).get g ≤ (t.next side).processed g.side) :
    (geometry s (t.next side) (moveCounters c side m)).height.get g +
        2 * ((moveCounters c side m).get g - c.get g) =
      (geometry s t c).height.get g + if side = g.side then 1 else 0 := by
  have hcounter := (moveCounters_between c side m g).1
  rw [Stage.processed_next] at hheightNew
  cases hs : s.sector <;> simp only [geometry, hs, Counters.get_ofFn, Stage.processed_next] <;>
    split_ifs at hheightNew ⊢ <;> omega

/-- Physical endpoint edits followed by FIFO removals give exactly the new native lengths. -/
theorem geometry_length_next_conservation (s : RunSpec) (t : Stage) (c : Counters)
    (side : Side) (m : Move) (g : Group)
    (hheight : 2 * c.get g ≤ t.processed g.side)
    (hheightNew : 2 * (moveCounters c side m).get g ≤ (t.next side).processed g.side)
    (hbudget : ∀ group, c.get group ≤ s.budgets.get group)
    (hbudgetNew : ∀ group, (moveCounters c side m).get group ≤ s.budgets.get group) :
    let old := geometry s t c
    let new := geometry s (t.next side) (moveCounters c side m)
    let oldJoined := min (old.emitted.get g) (old.emitted.get g.other)
    let newJoined := min (new.emitted.get g) (new.emitted.get g.other)
    new.length.get g + (newJoined - oldJoined) +
        2 * ((moveCounters c side m).get g - c.get g) =
      old.length.get g + if side = g.side then 1 else 0 := by
  dsimp only
  have hlen := geometry_length_add_joined s t c g
  have hlenNew := geometry_length_add_joined s (t.next side) (moveCounters c side m) g
  have hheightStep := geometry_height_next_conservation s t c side m g hheight hheightNew
  have hjoined := (joined_next_between s t c side m g hbudget hbudgetNew).1
  split_ifs at hheightStep ⊢ <;> omega

end Meanders.FirstCrossing
