import Meanders.Models.FirstCrossing.Interpretation.SourceStep
import Meanders.Models.FirstCrossing.Interpretation.SourceProgress
import Meanders.Models.FirstCrossing.Native.Stage

/-! Exact original lower-return observer, including the one through-arch bonus. -/

namespace Meanders.FirstCrossing

open DyckStep

/-- Indicator of an original inward lower down step beginning at height one. -/
def returnIndicator (w : List DyckStep) (i : ℕ) : ℕ :=
  if w[i]? = some D ∧ height w i = 1 then 1 else 0

/-- Number of original return events within the first `i` inward letters. -/
def returnPrefix (w : List DyckStep) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, returnIndicator w j

/-- Reading one more original letter adds precisely its return indicator. -/
theorem returnPrefix_succ (w : List DyckStep) (i : ℕ) :
    returnPrefix w (i + 1) = returnPrefix w i + returnIndicator w i := by
  exact Finset.sum_range_succ _ _

/-- The full indicator sum is the cardinality of the established return-event type. -/
theorem returnPrefix_full (w : List DyckStep) :
    returnPrefix w w.length = Fintype.card (ReturnEvent w) := by
  classical
  change returnPrefix w w.length =
    Fintype.card {i : Fin w.length // w[i.val]? = some D ∧ height w i.val = 1}
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  simpa only [returnPrefix, returnIndicator] using
    (Fin.sum_univ_eq_sum_range (fun i => returnIndicator w i) w.length).symm

/-- The native lower observer reads original down counters and original height,
independently of retained ports or any FIFO contractions. -/
theorem Source.lowerIncrement_return {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (side : Side) (key : Key)
    (hkey : key.counters = s.counters t) :
    lowerIncrement t key (s.nextMove t side) side =
      returnIndicator (s.word (Group.onSide false side)) (t.processed side) := by
  have hside : (Group.onSide false side).side = side := by cases side <;> rfl
  have hh := height_eq_original_downs (s.word (Group.onSide false side))
    (t.processed side) (by simpa only [hside] using
      (s.progress_length ht (Group.onSide false side)))
  have hn := s.word_nonneg (Group.onSide false side) (t.processed side)
  have he : t.processed side - 2 * (s.counters t).get (Group.onSide false side) = 1 ↔
      height (s.word (Group.onSide false side)) (t.processed side) = 1 := by
    simp only [Source.counters, Counters.get_ofFn, hside]
    omega
  simp only [lowerIncrement, hkey, s.nextMove_lowerDown, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, he, returnIndicator]

/-- Cumulative returns in the two original inward lower words at physical progress. -/
def Source.lowerReturns {spec : RunSpec} (s : Source spec) (t : Stage) : ℕ :=
  returnPrefix (s.word .ql) t.left + returnPrefix (s.word .qr) t.right

/-- One scheduled source label advances the original lower return sum exactly
by the executable increment. -/
theorem Source.lowerReturns_next {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (side : Side) (key : Key)
    (hkey : key.counters = s.counters t) :
    s.lowerReturns (t.next side) = s.lowerReturns t +
      lowerIncrement t key (s.nextMove t side) side := by
  rw [s.lowerIncrement_return ht side key hkey]
  cases side <;> simp [Source.lowerReturns, Stage.next, Stage.processed,
    Group.onSide, returnPrefix_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The actual source label's observer at one scheduled tick; the absent-tick
branch is outside the finite completed sum. -/
def Source.scheduledLowerIncrement {spec : RunSpec} (s : Source spec) (tick : ℕ) : ℕ :=
  match spec.schedule[tick]? with
  | none => 0
  | some side => lowerIncrement (Stage.ofTick spec tick)
      ⟨s.counters (Stage.ofTick spec tick), []⟩
      (s.nextMove (Stage.ofTick spec tick) side) side

/-- Exact telescoping of all actual scheduled source-label observer increments. -/
theorem Source.scheduledLower_sum {spec : RunSpec} (s : Source spec) {tick : ℕ}
    (htick : tick ≤ 2 * spec.n) :
    (∑ i ∈ Finset.range tick, s.scheduledLowerIncrement i) =
      s.lowerReturns (Stage.ofTick spec tick) := by
  induction tick with
  | zero => simp [Source.lowerReturns, Stage.ofTick, returnPrefix]
  | succ tick ih =>
    have hi : tick < spec.schedule.length := by rw [s.schedule_length]; omega
    let side := spec.schedule[tick]
    have hside : spec.schedule[tick]? = some side := List.getElem?_eq_getElem hi
    rw [Finset.sum_range_succ, ih (by omega), Stage.ofTick_next spec tick hside]
    rw [s.lowerReturns_next (s.ofTick_progress tick) side
      ⟨s.counters (Stage.ofTick spec tick), []⟩ rfl]
    simp only [Source.scheduledLowerIncrement, hside]

/-- HIGH has exactly one lower through-arch mark when its lower cut height is
positive; LOW has no through arch. -/
def Sector.lowerBonus : Sector → ℕ
  | .low => 0
  | .high _ _ v => if 0 < v then 1 else 0

/-- The source's lower bonus is precisely the original lower matching cut-height test. -/
theorem Source.lowerBonus_eq {spec : RunSpec} (s : Source spec) :
    spec.sector.lowerBonus = if 0 < height s.matchings.2.wordOf s.cut then 1 else 0 := by
  cases hs : spec.sector with
  | low =>
    have hz := (Balanced.of_isDyck s.matchings.2.isDyck_wordOf).height_length
    simpa only [Sector.lowerBonus, Source.cut, hs, s.matchings.2.length_wordOf] using
      (show 0 = if 0 < height s.matchings.2.wordOf (2 * spec.n) then 1 else 0 by
        rw [← s.matchings.2.length_wordOf, hz]
        decide)
  | high L u v =>
    have hh : height s.matchings.2.wordOf L = v := by
      have hin := s.inSector
      rw [hs] at hin
      exact hin.2.2
    simp only [Sector.lowerBonus, Source.cut, hs, hh, Nat.cast_pos]

/-- Summing the native lower observer over the complete scheduled source labels,
then adding the single HIGH bonus, counts the original lower exterior arches. -/
theorem Source.scheduledLower_exterior {spec : RunSpec} (s : Source spec) :
    (∑ i ∈ Finset.range (2 * spec.n), s.scheduledLowerIncrement i) +
      spec.sector.lowerBonus = s.matchings.2.exteriorArches.card := by
  rw [s.scheduledLower_sum le_rfl, Source.lowerReturns, s.ofTick_end]
  have hleft : s.cut = (s.word .ql).length := by
    rw [s.word_length, s.sideLength_eq]
    rfl
  have hright : 2 * spec.n - s.cut = (s.word .qr).length := by
    rw [s.word_length, s.sideLength_eq]
    rfl
  simp only at *
  rw [hright, hleft, returnPrefix_full, returnPrefix_full, s.lowerBonus_eq]
  have hlword : s.word .ql = s.matchings.2.wordOf.take s.cut := s.word_left false
  have hrword : s.word .qr = Dyck.reverseComplement (s.matchings.2.wordOf.drop s.cut) :=
    s.word_right false
  rw [congrArg (fun w => Fintype.card (ReturnEvent w)) hlword,
    congrArg (fun w => Fintype.card (ReturnEvent w)) hrword]
  exact (exteriorCount_cut s.matchings.2 s.cut_le).symm

end Meanders.FirstCrossing
