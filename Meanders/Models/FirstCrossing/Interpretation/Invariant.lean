import Meanders.Models.FirstCrossing.Original.Incidence
import Meanders.Models.FirstCrossing.Interpretation.SourceHalves
import Meanders.Models.FirstCrossing.Interpretation.FIFO
import Meanders.Models.FirstCrossing.Native.Geometry

/-!
# Physical source-prefix interpretation of the shared carrier

Original words determine every down counter and every retained endpoint.
The partial physical graph contains only visited crossings, internally closed
half arches, and the shared emitted prefix of through arches. In particular,
it does not import all edges of the completed matching pair.

This file establishes the interpretation's concrete data and its length
contract. Equivalence of native transitions to updates of this interpretation
is a separate preservation theorem.
-/

namespace Meanders.FirstCrossing

open SimpleGraph

/-- Every old opening occupies one of the levels below the final ballot height. -/
theorem BallotHalf.oldOpening_level_bound {len h l : Nat} (a : BallotHalf len h)
    (hl : l ∈ oldOpenings a.word) : (height a.word l).toNat < h := by
  obtain ⟨hll, hU, hn⟩ := mem_oldOpenings.mp hl
  have hh := (opening_unpaired_iff_above hll hU).mp hn a.word.length hll le_rfl
  change height a.word l < Dyck.height a.word at hh
  rw [a.height_word] at hh
  have hz := a.prefix_nonneg l
  rw [Dyck.height_take] at hz
  omega

theorem BallotHalf.oldOpenings_card {len h : Nat} (a : BallotHalf len h) :
    (oldOpenings a.word).card = h := by
  have he : (oldOpenings a.word).filter (fun l => (height a.word l).toNat < h) =
      oldOpenings a.word := by
    classical
    exact Finset.filter_true_of_mem (fun l hl => a.oldOpening_level_bound hl)
  rw [← he]
  exact a.oldOpenings_below_card le_rfl

/-- LOW uses the final physical cut, with empty right halves. -/
def Source.cut {spec : RunSpec} (_s : Source spec) : Nat :=
  match spec.sector with
  | .low => 2 * spec.n
  | .high L _ _ => L

/-- Every source cut lies inside its physical boundary. -/
theorem Source.cut_le {spec : RunSpec} (s : Source spec) : s.cut ≤ 2 * spec.n := by
  rcases spec with ⟨n, K, sector⟩
  cases sector with
  | low => exact le_rfl
  | high L u v => exact HighSource.cut_le s

/-- Original inward word of one fixed owner/side group; LOW right words are empty. -/
def Source.word {spec : RunSpec} (s : Source spec) (g : Group) : List DyckStep :=
  match spec, g with
  | ⟨_, _, .low⟩, .pl => s.upper.word
  | ⟨_, _, .low⟩, .ql => s.lower.word
  | ⟨_, _, .low⟩, .pr | ⟨_, _, .low⟩, .qr => []
  | ⟨_, _, .high _ _ _⟩, .pl => s.pl.word
  | ⟨_, _, .high _ _ _⟩, .pr => s.pr.word
  | ⟨_, _, .high _ _ _⟩, .ql => s.ql.word
  | ⟨_, _, .high _ _ _⟩, .qr => s.qr.word

theorem Source.word_length {spec : RunSpec} (s : Source spec) (g : Group) :
    (s.word g).length = spec.sideLength g.side := by
  rcases spec with ⟨n, K, sector⟩
  cases sector with
  | low =>
    change LowSource n K at s
    cases g <;> simp [word, RunSpec.sideLength, Group.side,
      s.upper.length_word, s.lower.length_word]
  | high L u v =>
    change HighSource n K L u v at s
    cases g <;> simp [word, RunSpec.sideLength, Group.side,
      s.pl.length_word, s.pr.length_word, s.ql.length_word, s.qr.length_word]

theorem Source.word_nonneg {spec : RunSpec} (s : Source spec)
    (g : Group) (i : Nat) : 0 ≤ height (s.word g) i := by
  rcases spec with ⟨n, K, sector⟩
  cases sector with
  | low =>
    change LowSource n K at s
    cases g
    · exact Dyck.height_take _ _ ▸ s.upper.prefix_nonneg i
    · simp [word, height]
    · exact Dyck.height_take _ _ ▸ s.lower.prefix_nonneg i
    · simp [word, height]
  | high L u v =>
    change HighSource n K L u v at s
    cases g
    · exact Dyck.height_take _ _ ▸ s.pl.prefix_nonneg i
    · exact Dyck.height_take _ _ ▸ s.pr.prefix_nonneg i
    · exact Dyck.height_take _ _ ▸ s.ql.prefix_nonneg i
    · exact Dyck.height_take _ _ ▸ s.qr.prefix_nonneg i

/-- Native budgets are the exact down counts of the original complete half words. -/
theorem Source.word_down_budget {spec : RunSpec} (s : Source spec) (g : Group) :
    (s.word g).count DyckStep.D = spec.budgets.get g := by
  rcases spec with ⟨n, K, sector⟩
  cases sector with
  | low =>
    change LowSource n K at s
    cases g <;> simp [word, RunSpec.budgets, Sector.budgets, Counters.ofTuple,
      Counters.get, s.upper.down_budget, s.lower.down_budget]
  | high L u v =>
    change HighSource n K L u v at s
    cases g <;> simp [word, RunSpec.budgets, Sector.budgets, Counters.ofTuple,
      Counters.get, s.pl.down_budget, s.pr.down_budget, s.ql.down_budget, s.qr.down_budget]

/-- The complete group word as a ballot half, shared across both sector forms. -/
def Source.wholeBallot {spec : RunSpec} (s : Source spec) (g : Group) :
    BallotHalf (spec.sideLength g.side) (Dyck.height (s.word g)).toNat where
  word := s.word g
  length_word := s.word_length g
  height_word := (Int.toNat_of_nonneg (s.word_nonneg g (s.word g).length)).symm
  prefix_nonneg i := Dyck.height_take _ _ ▸ s.word_nonneg g i

/-- Each left inward word is the original matching word up to the physical cut. -/
theorem Source.word_left {spec : RunSpec} (s : Source spec) (owner : Bool) :
    s.word (Group.onSide owner .left) =
      (ownerMatching s.matchings owner).wordOf.take s.cut := by
  rcases spec with ⟨n, K, sector⟩
  cases sector with
  | low =>
    change LowSource n K at s
    cases owner
    · change s.lower.word = (fullBallotEquiv n s.lower).wordOf.take (2 * n)
      rw [wordOf_fullBallotEquiv]
      simp [← s.lower.length_word]
    · change s.upper.word = (fullBallotEquiv n s.upper).wordOf.take (2 * n)
      rw [wordOf_fullBallotEquiv]
      simp [← s.upper.length_word]
  | high L u v =>
    change HighSource n K L u v at s
    cases owner
    · change s.ql.word = (HighSource.matchings s).2.wordOf.take L
      rw [HighSource.wordOf_lower, take_joinHalves]
    · change s.pl.word = (HighSource.matchings s).1.wordOf.take L
      rw [HighSource.wordOf_upper, take_joinHalves]

/-- Each right inward word is exactly the reflected physical suffix. -/
theorem Source.word_right {spec : RunSpec} (s : Source spec) (owner : Bool) :
    s.word (Group.onSide owner .right) =
      Dyck.reverseComplement ((ownerMatching s.matchings owner).wordOf.drop s.cut) := by
  rcases spec with ⟨n, K, sector⟩
  cases sector with
  | low =>
    change LowSource n K at s
    cases owner
    · change [] = Dyck.reverseComplement ((fullBallotEquiv n s.lower).wordOf.drop (2 * n))
      rw [wordOf_fullBallotEquiv]
      simp [← s.lower.length_word]
    · change [] = Dyck.reverseComplement ((fullBallotEquiv n s.upper).wordOf.drop (2 * n))
      rw [wordOf_fullBallotEquiv]
      simp [← s.upper.length_word]
  | high L u v =>
    change HighSource n K L u v at s
    cases owner
    · exact (HighSource.right_suffixes s).2.symm
    · exact (HighSource.right_suffixes s).1.symm

/-- Counters count original down steps; source joins have no effect on them. -/
def Source.counters {spec : RunSpec} (s : Source spec) (t : Stage) : Counters :=
  Counters.ofFn fun g => downs (s.word g) (t.processed g.side)

/-- A source prefix lies inside each original half. This does not assert any
native-state validity or path-representation conclusion. -/
def Source.Progress {spec : RunSpec} (s : Source spec) (t : Stage) : Prop :=
  t.left ≤ s.cut ∧ t.right ≤ 2 * spec.n - s.cut

theorem Source.progress_length {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) :
    t.processed g.side ≤ (s.word g).length := by
  rw [s.word_length]
  cases hs : spec.sector <;> cases g <;>
    simp_all [Progress, Source.cut, RunSpec.sideLength, Group.side, Stage.processed]

/-- The actual original prefix, bundled as a ballot half. -/
def Source.prefixBallot {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) :
    BallotHalf (t.processed g.side) (height (s.word g) (t.processed g.side)).toNat where
  word := (s.word g).take (t.processed g.side)
  length_word := by simp [List.length_take, Nat.min_eq_left (s.progress_length ht g)]
  height_word := by
    rw [Dyck.height_take]
    exact (Int.toNat_of_nonneg (s.word_nonneg g _)).symm
  prefix_nonneg i := by
    rw [List.take_take, Dyck.height_take]
    exact s.word_nonneg g _

/-- Original height agrees with the height reconstructed from the raw counters. -/
theorem Source.prefix_height {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) :
    (height (s.word g) (t.processed g.side)).toNat =
      (geometry spec t (s.counters t)).height.get g := by
  have hh := height_eq_original_downs (s.word g) _ (s.progress_length ht g)
  have hn := s.word_nonneg g (t.processed g.side)
  cases hs : spec.sector <;> simp only [geometry, hs, counters, Counters.get_ofFn] <;> omega

/-- An emitted old opening is a genuine through opening in the completed half,
with exactly its original ordinal. This is about the source, before key preservation. -/
theorem Source.emitted_opening_survives {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) {l : Nat}
    (hl : l ∈ oldOpenings ((s.word g).take (t.processed g.side)))
    (he : ((oldOpenings ((s.word g).take (t.processed g.side))).filter (· < l)).card <
      (geometry spec t (s.counters t)).emitted.get g) :
    l ∈ oldOpenings (s.word g) ∧
      ((oldOpenings (s.word g)).filter (· < l)).card =
        ((oldOpenings ((s.word g).take (t.processed g.side))).filter (· < l)).card := by
  classical
  cases hs : spec.sector with
  | low => cases g <;> simp [geometry, hs, Counters.zero, Counters.get] at he
  | high L u v =>
    have hbudget : (s.counters t).get g ≤ spec.budgets.get g := by
      rw [← s.word_down_budget]
      simpa only [counters, Counters.get_ofFn, downs] using
        (List.take_sublist (t.processed g.side) (s.word g)).count_le DyckStep.D
    rw [emitted_eq_originalCounters spec t (s.counters t) g hs hbudget] at he
    have hi := s.progress_length ht g
    rw [s.word_length] at hi
    have hf : l ∈ forcedOpenings (s.prefixBallot ht g)
        ((s.wholeBallot g).word.count DyckStep.D)
        (spec.sideLength g.side - t.processed g.side) := by
      apply ((s.prefixBallot ht g).emitted_mem_iff (s.wholeBallot g) hi rfl).mpr
      refine ⟨hl, ?_⟩
      simpa only [wholeBallot, prefixBallot, s.word_down_budget, counters,
        Counters.get_ofFn, downs] using he
    exact ⟨(s.prefixBallot ht g).forcedOpening_mem_completion (s.wholeBallot g) hi rfl hf,
      (s.prefixBallot ht g).forcedOpening_completion_ordinal (s.wholeBallot g) hi rfl hf⟩

/-- Old original opening indices in chronological, oldest-first order. -/
noncomputable def Source.openingIndices {spec : RunSpec}
    (s : Source spec) (t : Stage) (g : Group) : List Nat :=
  (oldOpenings ((s.word g).take (t.processed g.side))).sort (· ≤ ·)

theorem Source.openingIndices_length {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) :
    (s.openingIndices t g).length = (geometry spec t (s.counters t)).height.get g := by
  rw [openingIndices, Finset.length_sort]
  change (oldOpenings (s.prefixBallot ht g).word).card = _
  rw [BallotHalf.oldOpenings_card, s.prefix_height ht]

/-- Number of through pairs already joined for the owner of this group. -/
def Source.joined {spec : RunSpec} (s : Source spec)
    (t : Stage) (g : Group) : Nat :=
  let e := (geometry spec t (s.counters t)).emitted
  min (e.get g) (e.get g.other)

/-- Source retained endpoints are old openings with the already joined shared
prefix deleted; each group's own chronological numbering remains unchanged. -/
noncomputable def Source.retainedIndices {spec : RunSpec}
    (s : Source spec) (t : Stage) (g : Group) : List Nat :=
  (s.openingIndices t g).drop (s.joined t g)

/-- Exact native length contract, including the reservoir and unmatched FIFO. -/
theorem Source.retainedIndices_length {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) :
    (s.retainedIndices t g).length =
      (geometry spec t (s.counters t)).length.get g := by
  rw [retainedIndices, List.length_drop, s.openingIndices_length ht]
  cases hs : spec.sector with
  | low => cases g <;> simp [joined, geometry, hs, Counters.get, Counters.zero, Group.other]
  | high L u v =>
    simp only [joined, geometry, hs, Counters.get_ofFn]
    omega

/-- `true` selects the upper owner, consistently with native `Group.onSide`. -/
def Group.upper : Group → Bool
  | .pl | .pr => true
  | .ql | .qr => false

theorem Source.sideLength_eq {spec : RunSpec} (s : Source spec) (side : Side) :
    spec.sideLength side = match side with
      | .left => s.cut
      | .right => 2 * spec.n - s.cut := by
  cases hs : spec.sector <;> cases side <;> simp [RunSpec.sideLength, Source.cut, hs]

/-- The original source matching seen in the group's inward coordinate system. -/
def Source.inwardMatching {spec : RunSpec} (s : Source spec) (g : Group) :
    NoncrossingMatching spec.n :=
  match g.side with
  | .left => ownerMatching s.matchings g.upper
  | .right => (ownerMatching s.matchings g.upper).reflect

/-- The inward words agree literally with matching prefixes in each orientation. -/
theorem Source.word_inward {spec : RunSpec} (s : Source spec) (g : Group) :
    s.word g = (s.inwardMatching g).wordOf.take (spec.sideLength g.side) := by
  rw [s.sideLength_eq]
  cases g
  · exact s.word_left true
  · exact (s.word_right true).trans ((reflected_cut_halves
      (ownerMatching s.matchings true) s.cut_le).1.symm)
  · exact s.word_left false
  · exact (s.word_right false).trans ((reflected_cut_halves
      (ownerMatching s.matchings false) s.cut_le).1.symm)

/-- A processed prefix is the same physical matching prefix used by opening updates. -/
theorem Source.prefix_inward {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) :
    (s.word g).take (t.processed g.side) =
      (s.inwardMatching g).wordOf.take (t.processed g.side) := by
  have hi := s.progress_length ht g
  rw [s.word_length] at hi
  rw [s.word_inward, List.take_take, Nat.min_eq_left hi]

/-- Inward positions on the right are mapped to physical points by reflection. -/
def sourcePoint {n : Nat} (side : Side) (i : Nat) (hi : i < 2 * n) : Point n :=
  match side with
  | .left => ⟨i, hi⟩
  | .right => Point.mirror (⟨i, hi⟩ : Point n)

theorem Source.retainedIndex_lt_processed {spec : RunSpec} (s : Source spec)
    (t : Stage) (g : Group) {i : Nat} (hi : i ∈ s.retainedIndices t g) :
    i < t.processed g.side := by
  have ho : i ∈ s.openingIndices t g := List.mem_of_mem_drop hi
  rw [openingIndices, Finset.mem_sort] at ho
  have hl := (mem_oldOpenings.mp ho).1
  simp only [List.length_take] at hl
  omega

theorem Source.retainedIndex_lt {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) {i : Nat}
    (hi : i ∈ s.retainedIndices t g) : i < 2 * spec.n := by
  have hl := s.retainedIndex_lt_processed t g hi
  have hcut := s.cut_le
  cases g <;> simp only [Group.side, Stage.processed] at hl <;>
    obtain ⟨hleft, hright⟩ := ht <;> omega

/-- Actual physical incidence vertices in one retained owner/side group. -/
noncomputable def Source.retainedGroup {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) : List (Incidence spec.n) :=
  (s.retainedIndices t g).attach.map fun i =>
    (g.upper, sourcePoint g.side i.val (s.retainedIndex_lt ht g i.property))

theorem Source.retainedGroup_length {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) :
    (s.retainedGroup ht g).length = (geometry spec t (s.counters t)).length.get g := by
  simp only [retainedGroup, List.length_map, List.length_attach]
  exact s.retainedIndices_length ht g

/-- Physical incidence list in the native PL, PR, QL, QR storage order. -/
noncomputable def Source.retainedBoundary {spec : RunSpec}
    (s : Source spec) {t : Stage} (ht : s.Progress t) : List (Incidence spec.n) :=
  s.retainedGroup ht .pl ++ s.retainedGroup ht .pr ++
    s.retainedGroup ht .ql ++ s.retainedGroup ht .qr

theorem Source.retainedBoundary_length {spec : RunSpec}
    (s : Source spec) {t : Stage} (ht : s.Progress t) :
    (s.retainedBoundary ht).length =
      (Ports.ofLengths (geometry spec t (s.counters t)).length).flat.length := by
  simp only [retainedBoundary, List.length_append, s.retainedGroup_length ht,
    Ports.flat, Ports.ofLengths, List.length_map, List.length_range, Counters.get]

/-- Physical crossings visited from the original left or reflected-right side. -/
def visited {n : Nat} (t : Stage) (a : Point n) : Prop :=
  a.val < t.left ∨ a.mirror.val < t.right

/-- Every retained endpoint is an actually visited physical incidence. -/
theorem Source.retainedGroup_visited {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) {a : Incidence spec.n}
    (ha : a ∈ s.retainedGroup ht g) : visited t a.2 := by
  obtain ⟨⟨i, hi⟩, _, rfl⟩ := List.mem_map.mp ha
  have hl := s.retainedIndex_lt_processed t g hi
  cases g <;> simp_all [visited, sourcePoint, Group.side, Stage.processed]

theorem Source.retainedBoundary_visited {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) {a : Incidence spec.n}
    (ha : a ∈ s.retainedBoundary ht) : visited t a.2 := by
  simp only [retainedBoundary, List.mem_append] at ha
  rcases ha with ((ha | ha) | ha) | ha
  · exact s.retainedGroup_visited ht .pl ha
  · exact s.retainedGroup_visited ht .pr ha
  · exact s.retainedGroup_visited ht .ql ha
  · exact s.retainedGroup_visited ht .qr ha

/-- The shared emitted ordinal determines which through arches are already
present. The test is symmetric in the arch's physical endpoints. -/
def Source.joinedThrough {spec : RunSpec} (s : Source spec)
    (t : Stage) (owner : Bool) (a b : Point spec.n) : Prop :=
  let m := ownerMatching s.matchings owner
  let count := s.joined t (Group.onSide owner .left)
  (a.val < s.cut ∧ s.cut ≤ b.val ∧ ((m.active s.cut).filter (· < a)).card < count) ∨
    (b.val < s.cut ∧ s.cut ≤ a.val ∧ ((m.active s.cut).filter (· < b)).card < count)

/-- Only an internal half arch or an already joined through ordinal is present. -/
def Source.matchingProcessed {spec : RunSpec} (s : Source spec)
    (t : Stage) (owner : Bool) (a b : Point spec.n) : Prop :=
  visited t a ∧ visited t b ∧
    ((a.val < s.cut ↔ b.val < s.cut) ∨ s.joinedThrough t owner a b)

instance {n : Nat} (t : Stage) (a : Point n) : Decidable (visited t a) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance {spec : RunSpec} (s : Source spec)
    (t : Stage) (owner : Bool) (a b : Point spec.n) :
    Decidable (s.matchingProcessed t owner a b) := by
  unfold Source.matchingProcessed Source.joinedThrough
  infer_instance

/-- The actual processed source graph; future source edges are absent. -/
def Source.partialGraph {spec : RunSpec} (s : Source spec)
    (t : Stage) : SimpleGraph (Incidence spec.n) where
  Adj a b :=
    (a.2 = b.2 ∧ a.1 ≠ b.1 ∧ visited t a.2) ∨
    (a.1 = b.1 ∧ (ownerMatching s.matchings a.1).partner a.2 = b.2 ∧
      s.matchingProcessed t a.1 a.2 b.2)
  symm := ⟨by
    intro a b h
    rcases h with ⟨hp, ho, hv⟩ | ⟨ho, hp, hv⟩
    · exact Or.inl ⟨hp.symm, ho.symm, hp ▸ hv⟩
    · refine Or.inr ⟨ho.symm, ?_, ?_⟩
      · rw [← ho, ← hp, NoncrossingMatching.partner_partner]
      · rw [← ho]
        obtain ⟨ha, hb, hs⟩ := hv
        refine ⟨hb, ha, ?_⟩
        rcases hs with hs | hs
        · exact Or.inl hs.symm
        · exact Or.inr (hs.elim Or.inr Or.inl)⟩
  loopless := ⟨by
    intro a h
    rcases h with ⟨_, hne, _⟩ | ⟨_, hp, _⟩
    · exact hne rfl
    · exact (ownerMatching s.matchings a.1).partner_ne a.2 hp⟩

instance {spec : RunSpec} (s : Source spec) (t : Stage) :
    DecidableRel (s.partialGraph t).Adj := by
  intro a b
  unfold Source.partialGraph Source.matchingProcessed Source.joinedThrough visited
  infer_instance

/-- All present edges are physical source edges, while unprocessed edges need
not be present. -/
theorem Source.partialGraph_le {spec : RunSpec} (s : Source spec)
    (t : Stage) : s.partialGraph t ≤ incidenceGraph s.matchings := by
  intro a b h
  rcases h with ⟨hp, ho, _⟩ | ⟨ho, hp, _⟩
  · exact Or.inl ⟨hp, ho⟩
  · exact Or.inr ⟨ho, hp⟩

/-- Exact local edge test: there is one possible crossing edge and one possible
same-owner matching edge, each present only after its own source event. -/
theorem Source.partialGraph_adj_iff {spec : RunSpec} (s : Source spec)
    (t : Stage) (a b : Incidence spec.n) :
    (s.partialGraph t).Adj a b ↔
      (b = (!a.1, a.2) ∧ visited t a.2) ∨
        (b = (a.1, (ownerMatching s.matchings a.1).partner a.2) ∧
          s.matchingProcessed t a.1 a.2 ((ownerMatching s.matchings a.1).partner a.2)) := by
  rcases a with ⟨a, x⟩
  rcases b with ⟨b, y⟩
  cases a <;> cases b <;>
    simp only [partialGraph, ne_eq, eq_comm, not_true_eq_false, false_and, and_false,
      true_and, false_or, Bool.not_false, Bool.not_true, Prod.mk.injEq, Bool.false_eq_true,
      and_congr_right_iff, not_false_eq_true, or_false]
  all_goals rintro rfl; rfl

/-- A visited incidence is a boundary port exactly when its matching edge has
not been processed; absent physical vertices have degree zero. -/
theorem Source.partialGraph_degree {spec : RunSpec} (s : Source spec)
    (t : Stage) (a : Incidence spec.n) :
    (s.partialGraph t).degree a =
      if visited t a.2 then
        if s.matchingProcessed t a.1 a.2 ((ownerMatching s.matchings a.1).partner a.2)
          then 2 else 1
      else 0 := by
  classical
  have hne : (!a.1, a.2) ≠ (a.1, (ownerMatching s.matchings a.1).partner a.2) := by
    intro he
    have ho := congrArg Prod.fst he
    cases a.1 <;> simp at ho
  by_cases hv : visited t a.2
  · rw [ite_eq_left hv]
    by_cases hm : s.matchingProcessed t a.1 a.2 ((ownerMatching s.matchings a.1).partner a.2)
    · have he : (s.partialGraph t).neighborFinset a =
          {(!a.1, a.2), (a.1, (ownerMatching s.matchings a.1).partner a.2)} := by
        ext b
        simp [s.partialGraph_adj_iff, hv, hm]
      simp [degree, he, hm, hne]
    · have he : (s.partialGraph t).neighborFinset a = {(!a.1, a.2)} := by
        ext b
        simp [s.partialGraph_adj_iff, hv, hm]
      simp [degree, he, hm]
  · have hm : ¬s.matchingProcessed t a.1 a.2 ((ownerMatching s.matchings a.1).partner a.2) :=
      fun h => hv h.1
    have he : (s.partialGraph t).neighborFinset a = ∅ := by
      ext b
      simp [s.partialGraph_adj_iff, hv, hm]
    simp [degree, he, hv]

theorem Source.partialGraph_degree_one_iff {spec : RunSpec}
    (s : Source spec) (t : Stage) (a : Incidence spec.n) :
    (s.partialGraph t).degree a = 1 ↔ visited t a.2 ∧
      ¬s.matchingProcessed t a.1 a.2 ((ownerMatching s.matchings a.1).partner a.2) := by
  rw [s.partialGraph_degree]
  split_ifs <;> simp_all

/-- Concrete source/key interpretation. The graph and its physical endpoint
list are computed from the source words and original progress, not supplied
as existential witnesses. This definition does not assert transition preservation. -/
def Source.RepresentsKey {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (x : Key) : Prop :=
  x.counters = s.counters t ∧ x.mate.length = (s.retainedBoundary ht).length ∧
    ∀ i j : Fin (s.retainedBoundary ht).length,
      ((s.partialGraph t).Reachable (s.retainedBoundary ht)[i.val]
          (s.retainedBoundary ht)[j.val] ↔
        i = j ∨ x.mate[i.val]? = some j.val)

theorem Source.retainedBoundary_zero {spec : RunSpec} (s : Source spec) :
    s.retainedBoundary (t := ⟨0, 0, 0⟩) (by exact ⟨Nat.zero_le _, Nat.zero_le _⟩) = [] := by
  classical
  simp [retainedBoundary, retainedGroup, retainedIndices, openingIndices, oldOpenings,
    Group.side, Stage.processed]

/-- The native empty key has the stated physical source interpretation. -/
theorem Source.representsKey_empty {spec : RunSpec} (s : Source spec) :
    s.RepresentsKey (t := ⟨0, 0, 0⟩) (by exact ⟨Nat.zero_le _, Nat.zero_le _⟩) Key.empty := by
  unfold RepresentsKey
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · rw [s.retainedBoundary_zero]
    rfl
  · intro i
    have hi := i.isLt
    simp only [s.retainedBoundary_zero, List.length_nil, Nat.not_lt_zero] at hi

end Meanders.FirstCrossing
