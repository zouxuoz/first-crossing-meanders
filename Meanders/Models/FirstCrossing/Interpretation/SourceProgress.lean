import Meanders.Models.FirstCrossing.Interpretation.JoinedVisited
import Meanders.Models.FirstCrossing.Original.Schedule

/-!
# Physical schedule progress and the completed source graph

The prescribed schedule visits the two disjoint physical halves exactly once.
Its terminal counters exhaust the original down budgets and all through ordinals,
so the completed partial graph is the full colored source incidence graph.
-/

namespace Meanders.FirstCrossing

/-- Every source schedule has exactly the full physical boundary length. -/
theorem Source.schedule_length {spec : RunSpec} (s : Source spec) :
    spec.schedule.length = 2 * spec.n := by
  cases hs : spec.sector with
  | low => simp [RunSpec.schedule, hs]
  | high L u v =>
    simpa only [RunSpec.schedule, hs] using
      (Sector.schedule_high_length (u := u) (v := v)
        (by simpa only [Source.cut, hs] using s.cut_le))

/-- The schedule's left visits are exactly the source cut length. -/
theorem Source.schedule_count_left {spec : RunSpec} (s : Source spec) :
    spec.schedule.count .left = s.cut := by
  cases hs : spec.sector with
  | low => simp [RunSpec.schedule, Source.cut, hs]
  | high L u v =>
    simpa only [RunSpec.schedule, Source.cut, hs] using
      (Sector.schedule_high_count_left (u := u) (v := v)
        (by simpa only [Source.cut, hs] using s.cut_le))

/-- The schedule's right visits are exactly the reflected suffix length. -/
theorem Source.schedule_count_right {spec : RunSpec} (s : Source spec) :
    spec.schedule.count .right = 2 * spec.n - s.cut := by
  cases hs : spec.sector with
  | low => simp [RunSpec.schedule, Source.cut, hs, List.count_replicate]
  | high L u v =>
    simpa only [RunSpec.schedule, Source.cut, hs] using
      (Sector.schedule_high_count_right (u := u) (v := v)
        (by simpa only [Source.cut, hs] using s.cut_le))

/-- Every actual schedule prefix lies inside both original physical halves. -/
theorem Source.ofTick_progress {spec : RunSpec} (s : Source spec) (tick : ℕ) :
    s.Progress (Stage.ofTick spec tick) := by
  constructor
  · exact ((List.take_sublist tick spec.schedule).count_le .left).trans_eq s.schedule_count_left
  · exact ((List.take_sublist tick spec.schedule).count_le .right).trans_eq s.schedule_count_right

private theorem side_counts_total (xs : List Side) :
    xs.count .left + xs.count .right = xs.length := by
  induction xs with
  | nil => simp
  | cons side xs ih => cases side <;> simp_all <;> omega

/-- Each schedule tick processes one new physical vertex. -/
theorem Source.ofTick_sum {spec : RunSpec} (s : Source spec) {tick : ℕ}
    (htick : tick ≤ 2 * spec.n) :
    (Stage.ofTick spec tick).left + (Stage.ofTick spec tick).right = tick := by
  change (spec.schedule.take tick).count .left + (spec.schedule.take tick).count .right = tick
  rw [side_counts_total, List.length_take, s.schedule_length, Nat.min_eq_left htick]

/-- The completed stage has exhausted exactly the two physical half lengths. -/
theorem Source.ofTick_end {spec : RunSpec} (s : Source spec) :
    Stage.ofTick spec (2 * spec.n) = ⟨2 * spec.n, s.cut, 2 * spec.n - s.cut⟩ := by
  unfold Stage.ofTick
  have he : spec.schedule.take (2 * spec.n) = spec.schedule := by
    rw [← s.schedule_length, List.take_length]
  simp only [he, s.schedule_count_left, s.schedule_count_right]

/-- Exhausting the physical visit count visits every physical point. -/
theorem visited_of_full_progress {n : ℕ} (t : Stage) (hsum : t.left + t.right = 2 * n)
    (a : Point n) : visited t a := by
  have ha := a.isLt
  unfold visited
  simp only [Point.mirror_val]
  omega

/-- Before all vertices have been visited, the first unread left position is unvisited. -/
theorem exists_unvisited_of_progress_lt {n : ℕ} (t : Stage)
    (hsum : t.left + t.right < 2 * n) : ∃ a : Point n, ¬ visited t a := by
  let a : Point n := ⟨t.left, by omega⟩
  refine ⟨a, ?_⟩
  simp only [visited, a, Point.mirror_val]
  omega

/-- All physical points are visited at the terminal source stage. -/
theorem Source.visited_ofTick_end {spec : RunSpec} (s : Source spec) (a : Point spec.n) :
    visited (Stage.ofTick spec (2 * spec.n)) a :=
  visited_of_full_progress _ (s.ofTick_sum le_rfl) a

/-- Terminal progress exhausts each original group's complete inward word. -/
theorem Source.ofTick_end_processed {spec : RunSpec} (s : Source spec) (g : Group) :
    (Stage.ofTick spec (2 * spec.n)).processed g.side = spec.sideLength g.side := by
  rw [s.ofTick_end, s.sideLength_eq]
  cases g <;> rfl

/-- Every terminal original down counter equals its prescribed source budget. -/
theorem Source.counters_end_get {spec : RunSpec} (s : Source spec) (g : Group) :
    (s.counters (Stage.ofTick spec (2 * spec.n))).get g = spec.budgets.get g := by
  rw [Source.counters, Counters.get_ofFn]
  unfold downs
  rw [s.ofTick_end_processed, ← s.word_length, List.take_length, s.word_down_budget]

/-- Opposite inward halves of one owner have the same final cut height. -/
theorem Source.word_height_other {spec : RunSpec} (s : Source spec) (g : Group) :
    Dyck.height (s.word g.other) = Dyck.height (s.word g) := by
  rcases spec with ⟨n, K, sector⟩
  cases sector with
  | low =>
    change LowSource n K at s
    cases g <;> simp [Source.word, Group.other, s.upper.height_word, s.lower.height_word]
  | high L u v =>
    change HighSource n K L u v at s
    cases g <;> simp [Source.word, Group.other, s.pl.height_word, s.pr.height_word,
      s.ql.height_word, s.qr.height_word]

/-- Terminal geometry reconstructs the original cut height in every group. -/
theorem Source.geometry_height_end {spec : RunSpec} (s : Source spec) (g : Group) :
    (geometry spec (Stage.ofTick spec (2 * spec.n))
      (s.counters (Stage.ofTick spec (2 * spec.n)))).height.get g =
        (Dyck.height (s.word g)).toNat := by
  rw [← s.prefix_height (s.ofTick_progress _) g, s.ofTick_end_processed, ← s.word_length]
  simp only [height, List.take_length, Dyck.height]

/-- All original unmatched openings have emitted by the terminal stage. -/
theorem Source.emitted_end {spec : RunSpec} (s : Source spec) (g : Group) :
    (geometry spec (Stage.ofTick spec (2 * spec.n))
      (s.counters (Stage.ofTick spec (2 * spec.n)))).emitted.get g =
        (Dyck.height (s.word g)).toNat := by
  cases hs : spec.sector with
  | low =>
    rcases spec with ⟨n, K, sector⟩
    cases hs
    change LowSource n K at s
    cases g <;> simp [geometry, Source.word, Counters.zero, Counters.get,
      s.upper.height_word, s.lower.height_word]
  | high L u v =>
    have hh := s.geometry_height_end g
    simp only [geometry, hs, Counters.get_ofFn] at hh ⊢
    rw [s.counters_end_get, Nat.sub_self, Nat.sub_zero]
    rwa [s.counters_end_get] at hh

/-- Every through ordinal has joined by the terminal physical stage. -/
theorem Source.joined_end {spec : RunSpec} (s : Source spec) (g : Group) :
    s.joined (Stage.ofTick spec (2 * spec.n)) g = (Dyck.height (s.word g)).toNat := by
  dsimp only [Source.joined]
  rw [s.emitted_end, s.emitted_end, s.word_height_other, Nat.min_self]

/-- Terminal FIFO joins exhaust the actual physical through arches of each owner. -/
theorem Source.joined_end_eq_active_card {spec : RunSpec} (s : Source spec) (owner : Bool) :
    s.joined (Stage.ofTick spec (2 * spec.n)) (Group.onSide owner .left) =
      ((ownerMatching s.matchings owner).active s.cut).card := by
  rw [s.joined_end, s.word_left, Dyck.height_take]
  have hh := (ownerMatching s.matchings owner).card_active s.cut_le
  omega

private theorem ordinal_lt_card {α : Type*} [LinearOrder α] (xs : Finset α)
    {a : α} (ha : a ∈ xs) : (xs.filter (· < a)).card < xs.card := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
  intro he
  have hh : a ∈ xs.filter (· < a) := he.symm ▸ ha
  exact lt_irrefl _ (Finset.mem_filter.mp hh).2

/-- At the terminal stage every actual matching edge is present, internal or through. -/
theorem Source.matchingProcessed_end {spec : RunSpec} (s : Source spec)
    (owner : Bool) (a : Point spec.n) :
    s.matchingProcessed (Stage.ofTick spec (2 * spec.n)) owner a
      ((ownerMatching s.matchings owner).partner a) := by
  let m := ownerMatching s.matchings owner
  refine ⟨s.visited_ofTick_end a, s.visited_ofTick_end (m.partner a), ?_⟩
  by_cases ha : a.val < s.cut <;> by_cases hb : (m.partner a).val < s.cut
  · exact Or.inl ⟨fun _ => hb, fun _ => ha⟩
  · apply Or.inr
    refine Or.inl ⟨ha, Nat.le_of_not_gt hb, ?_⟩
    rw [s.joined_end_eq_active_card]
    exact ordinal_lt_card _ (m.mem_active.mpr ⟨ha, Nat.le_of_not_gt hb⟩)
  · apply Or.inr
    refine Or.inr ⟨hb, Nat.le_of_not_gt ha, ?_⟩
    rw [s.joined_end_eq_active_card]
    have hactive : m.partner a ∈ m.active s.cut :=
      m.mem_active.mpr ⟨hb, by rw [m.partner_partner]; exact Nat.le_of_not_gt ha⟩
    exact ordinal_lt_card _ hactive
  · exact Or.inl ⟨fun h => False.elim (ha h), fun h => False.elim (hb h)⟩

/-- The completed physical source graph is exactly its full colored incidence graph. -/
theorem Source.partialGraph_end {spec : RunSpec} (s : Source spec) :
    s.partialGraph (Stage.ofTick spec (2 * spec.n)) = incidenceGraph s.matchings := by
  apply le_antisymm (s.partialGraph_le _)
  intro a b h
  rcases h with ⟨hp, ho⟩ | ⟨ho, hp⟩
  · exact Or.inl ⟨hp, ho, s.visited_ofTick_end a.2⟩
  · refine Or.inr ⟨ho, hp, ?_⟩
    rw [← hp]
    exact s.matchingProcessed_end a.1 a.2

end Meanders.FirstCrossing
