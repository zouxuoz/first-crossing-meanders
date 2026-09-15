import Meanders.Models.FirstCrossing.Packed.Codec
import Meanders.Models.FirstCrossing.Native.Transition

/-!
# Packed storage refinement of the native labelled successor

The mathematical packed successor reuses the proved native surgery and exact
lower increment through the concrete bit codec. Capacity is an explicit premise
of the machine-word refinement, not a new pruning rule. Labelled collisions are
retained by the fixed four-label list.
-/

namespace Meanders.FirstCrossing.Packed

/-- The same checked physical transition, storing its result in the exact cyclic bit codec. -/
def rawStep (s : RunSpec) (t : Stage) (k : Key) (m : Move) : Option Key := do
  let side ← s.schedule[t.tick]?
  let out ← FirstCrossing.rawStep s t (decode s t k) m
  return encode s (t.next side) out

/-- The observer reads original decoded counters and keeps the native increment unchanged. -/
def step (s : RunSpec) (t : Stage) (k : Key) (m : Move) : Option (Key × Nat) := do
  let side ← s.schedule[t.tick]?
  let out ← rawStep s t k m
  return (out, lowerIncrement t (decode s t k) m side)

/-- The four original labels enumerate successors with their exact multiplicity. -/
def successors (s : RunSpec) (t : Stage) (k : Key) : List (Key × Nat) :=
  Move.all.filterMap (step s t k)

/-- Decoding every possible output recovers the exact native raw transition. -/
theorem decode_rawStep {s : RunSpec} {t : Stage} (k : Key) {side : Side}
    (hs : s.schedule[t.tick]? = some side) (m : Move) :
    (rawStep s t k m).map (decode s (t.next side)) =
      FirstCrossing.rawStep s t (decode s t k) m := by
  unfold rawStep
  simp only [hs]
  cases he : FirstCrossing.rawStep s t (decode s t k) m with
  | none => rfl
  | some out =>
    obtain ⟨side', hs', hv⟩ := rawStep_valid he
    have hside : side' = side := Option.some.inj (hs'.symm.trans hs)
    subst side'
    change some (decode s (t.next side) (encode s (t.next side) out)) = some out
    exact congrArg some (decode_encode s (t.next side) out hv)

/-- Decoding a labelled edge preserves the lower increment, including rejection. -/
theorem decode_step {s : RunSpec} {t : Stage} (k : Key) {side : Side}
    (hs : s.schedule[t.tick]? = some side) (m : Move) :
    (step s t k m).map (fun edge => (decode s (t.next side) edge.1, edge.2)) =
      FirstCrossing.step s t (decode s t k) m := by
  have hr := decode_rawStep k hs m
  simp only [step, FirstCrossing.step, hs]
  cases hp : rawStep s t k m with
  | none =>
    simp only [hp, Option.map_none] at hr
    rw [← hr]
    rfl
  | some out =>
    simp only [hp, Option.map_some] at hr
    rw [← hr]
    rfl

/-- Missing schedule positions reject every label in both representations. -/
theorem step_none_of_schedule_none {s : RunSpec} {t : Stage} (k : Key)
    (hs : s.schedule[t.tick]? = none) (m : Move) : step s t k m = none := by
  simp [step, hs]

end Meanders.FirstCrossing.Packed
