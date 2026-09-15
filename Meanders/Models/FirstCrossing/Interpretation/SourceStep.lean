import Meanders.Models.FirstCrossing.Interpretation.OpeningStep
import Meanders.Models.FirstCrossing.Interpretation.Invariant

/-! Complete source words discharge the original-counter feasibility guards. -/

namespace Meanders.FirstCrossing

/-- Feasible complete source halves satisfy every original-counter guard at each prefix. -/
theorem Source.counters_valid {spec : RunSpec} (s : Source spec) {t : Stage}
    (ht : s.Progress t) : countersValid spec t (s.counters t) = true := by
  unfold countersValid
  apply List.all_eq_true.mpr
  intro g _
  apply decide_eq_true
  have hi := s.progress_length ht g
  have hh := height_eq_original_downs (s.word g) _ hi
  have hn := s.word_nonneg g (t.processed g.side)
  have hc : downs (s.word g) (t.processed g.side) ≤ spec.budgets.get g := by
    rw [← s.word_down_budget]
    exact (List.take_sublist _ _).count_le _
  have hsplit := congrArg (fun w : List DyckStep => w.count DyckStep.D)
    (List.take_append_drop (t.processed g.side) (s.word g))
  simp only [List.count_append, s.word_down_budget] at hsplit
  have hdrop := List.count_le_length (a := DyckStep.D)
    (l := (s.word g).drop (t.processed g.side))
  rw [List.length_drop, s.word_length] at hdrop
  rw [s.word_length] at hi
  simp only [Source.counters, Counters.get_ofFn]
  unfold downs at hh hc ⊢
  omega

/-- The native truncated grade equals the original physical grade on actual sources. -/
theorem Source.prefix_grade {spec : RunSpec} (s : Source spec) {t : Stage}
    (ht : s.Progress t) :
    ((t.left - (s.counters t).pl - (s.counters t).ql : ℕ) : ℤ) =
      grade s.matchings.1 s.matchings.2 t.left := by
  have hpl : downs (s.word .pl) t.left = downs s.matchings.1.wordOf t.left := by
    have he := s.word_left true
    simpa [Group.onSide, ownerMatching, downs, List.take_take,
      Nat.min_eq_left ht.1] using congrArg (fun w => downs w t.left) he
  have hql : downs (s.word .ql) t.left = downs s.matchings.2.wordOf t.left := by
    have he := s.word_left false
    simpa [Group.onSide, ownerMatching, downs, List.take_take,
      Nat.min_eq_left ht.1] using congrArg (fun w => downs w t.left) he
  have hp := s.word_nonneg .pl t.left
  have hq := s.word_nonneg .ql t.left
  rw [height_eq_original_downs _ _ (by
    simpa [Group.side, Stage.processed] using s.progress_length ht .pl)] at hp
  rw [height_eq_original_downs _ _ (by
    simpa [Group.side, Stage.processed] using s.progress_length ht .ql)] at hq
  simp only [Source.counters, Counters.ofFn, grade]
  simp only [Group.side, Stage.processed, hpl, hql] at hp hq ⊢
  omega

/-- The chronological first-height guard follows from the direct source-sector predicate. -/
theorem Source.prefix_allowed {spec : RunSpec} (s : Source spec) {t : Stage}
    (ht : s.Progress t) : prefixAllowed spec t (s.counters t) = true := by
  have hg := s.prefix_grade ht
  have hs := s.inSector
  have hl := ht.1
  cases hsector : spec.sector with
  | low =>
    have hlen : t.left ≤ 2 * spec.n := by simpa [Source.cut, hsector] using hl
    have hlow : Low spec.K s.matchings.1 s.matchings.2 := by
      simpa only [hsector, InSector] using hs
    have hk := hlow t.left hlen
    simp only [prefixAllowed, hsector, decide_eq_true_eq]
    omega
  | high L u v =>
    have hhit : FirstHit spec.K s.matchings.1 s.matchings.2 L := by
      have he : InSector spec.K s.matchings.1 s.matchings.2 (.high L u v) := by
        simpa only [hsector] using hs
      exact he.1
    have hleft : t.left ≤ L := by simpa [Source.cut, hsector] using hl
    simp only [prefixAllowed, hsector]
    split
    · rename_i hi
      have hk := hhit.2.2 t.left hi
      apply decide_eq_true
      omega
    · rename_i hi
      have he : t.left = L := by omega
      rw [he] at hg
      rw [hhit.2.1] at hg
      apply decide_eq_true
      omega

end Meanders.FirstCrossing

/-!
# The original source supplies a legal local label

The next label reads the two original owner words. Local counter and prefix
checks follow from those words; no port or path representation is assumed.
-/

namespace Meanders.FirstCrossing

open DyckStep

/-- Read the original two owner letters; beyond a half, missing letters default to U. -/
def Source.nextMove {spec : RunSpec} (s : Source spec) (t : Stage) (side : Side) : Move :=
  let upper := (s.word (Group.onSide true side))[t.processed side]? = some D
  let lower := (s.word (Group.onSide false side))[t.processed side]? = some D
  if upper then (if lower then .DD else .DU) else (if lower then .UD else .UU)

@[simp] theorem Source.nextMove_upperDown {spec : RunSpec} (s : Source spec)
    (t : Stage) (side : Side) :
    (s.nextMove t side).upperDown =
      decide ((s.word (Group.onSide true side))[t.processed side]? = some D) := by
  simp only [nextMove]
  split_ifs <;> simp_all [Move.upperDown]

@[simp] theorem Source.nextMove_lowerDown {spec : RunSpec} (s : Source spec)
    (t : Stage) (side : Side) :
    (s.nextMove t side).lowerDown =
      decide ((s.word (Group.onSide false side))[t.processed side]? = some D) := by
  simp only [nextMove]
  split_ifs <;> simp_all [Move.lowerDown]

private theorem downs_succ_indicator (w : List DyckStep) (i : ℕ) :
    downs w (i + 1) = downs w i + (decide (w[i]? = some D)).toNat := by
  cases he : w[i]? with
  | none => simp [downs, List.take_add_one, he]
  | some step => cases step <;> simp [downs, List.take_add_one, he]

/-- Reading the source label advances exactly its original down counters. -/
theorem Source.nextMove_counters {spec : RunSpec} (s : Source spec) (t : Stage) (side : Side) :
    moveCounters (s.counters t) side (s.nextMove t side) = s.counters (t.next side) := by
  cases side <;>
    simp [moveCounters, Source.counters, Counters.ofFn, Counters.get, Counters.set,
      Group.onSide, Group.side, Stage.next, Stage.processed, downs_succ_indicator]

/-- A real source D has positive original height and at least one remaining down. -/
theorem Source.down_original_pos {spec : RunSpec} (s : Source spec) {t : Stage}
    (ht : s.Progress t) (g : Group)
    (hD : (s.word g)[t.processed g.side]? = some D) :
    0 < t.processed g.side - 2 * (s.counters t).get g ∧
      (s.counters t).get g < spec.budgets.get g := by
  have hh := height_eq_original_downs (s.word g) _ (s.progress_length ht g)
  have hn := s.word_nonneg g (t.processed g.side + 1)
  rw [height_succ_of_D hD] at hn
  have hb := (List.take_sublist (t.processed g.side + 1) (s.word g)).count_le D
  change downs (s.word g) (t.processed g.side + 1) ≤ (s.word g).count D at hb
  rw [downs_succ_of_D hD, s.word_down_budget g] at hb
  simp only [Source.counters, Counters.get_ofFn]
  omega

/-- Every actual source D consumes an unforced reservoir endpoint. -/
theorem Source.down_reservoir_pos {spec : RunSpec} (s : Source spec) {t : Stage}
    (ht : s.Progress t) (g : Group)
    (hD : (s.word g)[t.processed g.side]? = some D) :
    0 < (geometry spec t (s.counters t)).reservoir.get g := by
  obtain ⟨hh, hb⟩ := s.down_original_pos ht g hD
  cases hs : spec.sector with
  | low => simpa [geometry, hs] using hh
  | high L u v =>
    rw [reservoir_eq_min spec t (s.counters t) g hs]
    omega

@[simp] private theorem side_onSide (owner : Bool) (side : Side) :
    (Group.onSide owner side).side = side := by cases side <;> cases owner <;> rfl

/-- Advancing an actual source prefix visits an existing letter on both owner words. -/
theorem Source.visit_lt {spec : RunSpec} (s : Source spec) {t : Stage} {side : Side}
    (hnext : s.Progress (t.next side)) : t.processed side < spec.sideLength side := by
  have hi := s.progress_length hnext (Group.onSide true side)
  rw [s.word_length] at hi
  simpa only [side_onSide, Stage.processed_next, ite_true, Nat.add_one_le_iff] using hi

/-- Both letters selected by the local label really exist; no fallback is used on a visit. -/
theorem Source.nextMove_letters {spec : RunSpec} (s : Source spec) {t : Stage} {side : Side}
    (hnext : s.Progress (t.next side)) :
    (s.word (Group.onSide true side))[t.processed side]? =
        some (if (s.nextMove t side).upperDown then D else U) ∧
      (s.word (Group.onSide false side))[t.processed side]? =
        some (if (s.nextMove t side).lowerDown then D else U) := by
  have hv := s.visit_lt hnext
  have hletter (owner : Bool) :
      (s.word (Group.onSide owner side))[t.processed side]? =
        some (if (s.word (Group.onSide owner side))[t.processed side]? = some D then D else U) := by
    have hi : t.processed side < (s.word (Group.onSide owner side)).length := by
      simpa only [s.word_length, side_onSide] using hv
    rcases getElem?_eq_U_or_D hi with hU | hD
    · simp [hU]
    · simp [hD]
  simpa only [nextMove_upperDown, nextMove_lowerDown, decide_eq_true_eq] using
    And.intro (hletter true) (hletter false)

/-- A direct source prefix exposes the checked remaining-budget bounds for one group. -/
private theorem Source.remaining_budget {spec : RunSpec} (s : Source spec) {t : Stage}
    (ht : s.Progress t) (g : Group) :
    (s.counters t).get g ≤ spec.budgets.get g ∧
      spec.budgets.get g - (s.counters t).get g ≤
        spec.sideLength g.side - t.processed g.side := by
  have hc := s.counters_valid ht
  unfold countersValid at hc
  have hg := List.all_eq_true.mp hc g (by cases g <;> simp [Group.all])
  have hh := of_decide_eq_true hg
  exact hh.2.2

/-- The original source's local label satisfies every native move guard. -/
theorem Source.nextMove_allowed {spec : RunSpec} (s : Source spec) {t : Stage} {side : Side}
    (ht : s.Progress t) (hnext : s.Progress (t.next side)) (x : Key)
    (hx : x.counters = s.counters t) :
    moveAllowed spec t x side (s.nextMove t side) = true := by
  have hv := s.visit_lt hnext
  have hup : (!(s.nextMove t side).upperDown ||
      decide (0 < (geometry spec t (s.counters t)).reservoir.get
        (Group.onSide true side))) = true := by
    by_cases hD : (s.word (Group.onSide true side))[t.processed side]? = some D
    · have hp := s.down_reservoir_pos ht (Group.onSide true side) (by simpa using hD)
      simp [hD, hp]
    · simp [hD]
  have hlo : (!(s.nextMove t side).lowerDown ||
      decide (0 < (geometry spec t (s.counters t)).reservoir.get
        (Group.onSide false side))) = true := by
    by_cases hD : (s.word (Group.onSide false side))[t.processed side]? = some D
    · have hp := s.down_reservoir_pos ht (Group.onSide false side) (by simpa using hD)
      simp [hD, hp]
    · simp [hD]
  have hb : [Group.onSide true side, Group.onSide false side].all (fun owner =>
      decide ((s.counters (t.next side)).get owner ≤ spec.budgets.get owner ∧
        spec.budgets.get owner - (s.counters (t.next side)).get owner ≤
          spec.sideLength side - t.processed side - 1)) = true := by
    apply List.all_eq_true.mpr
    intro g hg
    have hgside : g.side = side := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> exact side_onSide _ _
    have hh := s.remaining_budget hnext g
    rw [hgside, Stage.processed_next] at hh
    simp only [ite_true] at hh
    apply decide_eq_true
    constructor
    · exact hh.1
    · omega
  simp only [moveAllowed, hx, s.nextMove_counters, hup, hlo, decide_eq_true hv,
    hb, Bool.true_and]
  cases side
  · exact s.prefix_allowed hnext
  · rfl

end Meanders.FirstCrossing
