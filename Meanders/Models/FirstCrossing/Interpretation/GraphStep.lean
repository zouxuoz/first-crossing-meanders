import Meanders.Models.FirstCrossing.Interpretation.Boundary
import Meanders.Models.FirstCrossing.Interpretation.SourceStep

/-!
# Exact physical edges added by a source visit

The edge events below are computed from original physical source matchings,
visited positions, and emitted ordinals. No successor path representation is
assumed. Both sectors use these same definitions.
-/

namespace Meanders.FirstCrossing

/-- Original prefix down counters never exceed their whole source-word budgets. -/
theorem Source.counter_le_budget {spec : RunSpec} (s : Source spec) (t : Stage) (g : Group) :
    (s.counters t).get g ≤ spec.budgets.get g := by
  rw [← s.word_down_budget g]
  simp only [Source.counters, Counters.get_ofFn, downs]
  exact (List.take_sublist (t.processed g.side) (s.word g)).count_le DyckStep.D

/-- A source visit joins zero or one additional through pair per owner. -/
theorem Source.joined_next_between {spec : RunSpec} (s : Source spec)
    (t : Stage) (side : Side) (g : Group) :
    s.joined t g ≤ s.joined (t.next side) g ∧
      s.joined (t.next side) g - s.joined t g ≤ 1 := by
  have h := FirstCrossing.joined_next_between spec t (s.counters t) side
    (s.nextMove t side) g (s.counter_le_budget t) (fun g => by
      rw [s.nextMove_counters]
      exact s.counter_le_budget (t.next side) g)
  simpa only [s.nextMove_counters, Source.joined] using h

/-- The next original inward position exists in the physical point set. -/
theorem Source.visit_lt_size {spec : RunSpec} (s : Source spec) {t : Stage} {side : Side}
    (hnext : s.Progress (t.next side)) : t.processed side < 2 * spec.n := by
  have hi := s.visit_lt hnext
  rw [s.sideLength_eq] at hi
  have hc := s.cut_le
  cases side <;> simp only at hi <;> omega

/-- The physical crossing visited by the next source letter. -/
def Source.newPoint {spec : RunSpec} (s : Source spec) {t : Stage} {side : Side}
    (hnext : s.Progress (t.next side)) : Point spec.n :=
  sourcePoint side (t.processed side) (s.visit_lt_size hnext)

/-- A visit adds exactly one physical point to the visited region. -/
theorem Source.visited_next_iff {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side)) (a : Point spec.n) :
    visited (t.next side) a ↔ visited t a ∨ a = s.newPoint hnext := by
  have ha := a.isLt
  have hi := s.visit_lt_size hnext
  cases side <;>
    simp only [visited, Stage.next, Source.newPoint, sourcePoint, Stage.processed,
      Fin.ext_iff, Point.mirror_val] <;> omega

/-- The newly visited physical point was absent before this visit. -/
theorem Source.newPoint_not_visited {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side)) :
    ¬visited t (s.newPoint hnext) := by
  obtain ⟨hl, hr⟩ := hnext
  have hc := s.cut_le
  cases side <;>
    simp only [Stage.next] at hl hr <;>
    simp only [visited, Source.newPoint, sourcePoint, Stage.processed,
      Point.mirror_mirror, Point.mirror_val] <;> omega

/-- A newly completed original internal-half edge attaches the new point to an
already visited point. The original matching relation is supplied separately. -/
def Source.internalAdded {spec : RunSpec} (s : Source spec) (t : Stage)
    (p a b : Point spec.n) : Prop :=
  (a.val < s.cut ↔ b.val < s.cut) ∧
    ((a = p ∧ visited t b) ∨ (b = p ∧ visited t a))

/-- A newly joined through edge has an original ordinal in the newly emitted
interval. This definition uses the original matching cut, not graph difference. -/
def Source.throughAdded {spec : RunSpec} (s : Source spec) (t : Stage) (side : Side)
    (owner : Bool) (a b : Point spec.n) : Prop :=
  let m := ownerMatching s.matchings owner
  let old := s.joined t (Group.onSide owner .left)
  let new := s.joined (t.next side) (Group.onSide owner .left)
  (a.val < s.cut ∧ s.cut ≤ b.val ∧ old ≤ ((m.active s.cut).filter (· < a)).card ∧
    ((m.active s.cut).filter (· < a)).card < new) ∨
  (b.val < s.cut ∧ s.cut ≤ a.val ∧ old ≤ ((m.active s.cut).filter (· < b)).card ∧
    ((m.active s.cut).filter (· < b)).card < new)

/-- The joined prefix grows exactly by the new ordinal interval. -/
theorem Source.joinedThrough_next_iff {spec : RunSpec} (s : Source spec)
    (t : Stage) (side : Side) (owner : Bool) (a b : Point spec.n) :
    s.joinedThrough (t.next side) owner a b ↔
      s.joinedThrough t owner a b ∨ s.throughAdded t side owner a b := by
  have hm := (s.joined_next_between t side (Group.onSide owner .left)).1
  simp only [Source.joinedThrough, Source.throughAdded]
  omega

/-- An original matching edge is added either by an internal D attachment or
by the next shared through ordinal, after retaining every existing edge. -/
theorem Source.matchingProcessed_next_iff {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (owner : Bool) (a : Point spec.n) :
    s.matchingProcessed (t.next side) owner a ((ownerMatching s.matchings owner).partner a) ↔
      s.matchingProcessed t owner a ((ownerMatching s.matchings owner).partner a) ∨
      s.internalAdded t (s.newPoint hnext) a ((ownerMatching s.matchings owner).partner a) ∨
      s.throughAdded t side owner a ((ownerMatching s.matchings owner).partner a) := by
  rw [s.matchingProcessed_iff hnext, s.matchingProcessed_iff ht,
    s.visited_next_iff hnext, s.visited_next_iff hnext, s.joinedThrough_next_iff]
  have hne := (ownerMatching s.matchings owner).partner_ne a
  simp only [Source.internalAdded]
  constructor
  · rintro (⟨ha | ha, hb | hb, hc⟩ | hj | hj)
    · exact Or.inl (Or.inl ⟨ha, hb, hc⟩)
    · exact Or.inr (Or.inl ⟨hc, Or.inr ⟨hb, ha⟩⟩)
    · exact Or.inr (Or.inl ⟨hc, Or.inl ⟨ha, hb⟩⟩)
    · exact False.elim (hne (hb.trans ha.symm))
    · exact Or.inl (Or.inr hj)
    · exact Or.inr (Or.inr hj)
  · rintro ((⟨ha, hb, hc⟩ | hj) | ⟨hc, (⟨ha, hb⟩ | ⟨hb, ha⟩)⟩ | hj)
    · exact Or.inl ⟨Or.inl ha, Or.inl hb, hc⟩
    · exact Or.inr (Or.inl hj)
    · exact Or.inl ⟨Or.inr ha, Or.inl hb, hc⟩
    · exact Or.inl ⟨Or.inl ha, Or.inr hb, hc⟩
    · exact Or.inr (Or.inr hj)

/-- Exact physical source-graph update: one crossing edge, original internal
attachments, and newly joined through edges. All event predicates use original
source positions and ordinals; successor connectivity is not a premise. -/
theorem Source.partialGraph_next_adj_iff {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (a b : Incidence spec.n) :
    (s.partialGraph (t.next side)).Adj a b ↔
      (s.partialGraph t).Adj a b ∨
      (a.2 = b.2 ∧ a.1 ≠ b.1 ∧ a.2 = s.newPoint hnext) ∨
      (a.1 = b.1 ∧ (ownerMatching s.matchings a.1).partner a.2 = b.2 ∧
        (s.internalAdded t (s.newPoint hnext) a.2 b.2 ∨
          s.throughAdded t side a.1 a.2 b.2)) := by
  simp only [Source.partialGraph]
  constructor
  · rintro (⟨hp, ho, hv⟩ | ⟨ho, hp, hm⟩)
    · rcases (s.visited_next_iff hnext a.2).mp hv with hv | hv
      · exact Or.inl (Or.inl ⟨hp, ho, hv⟩)
      · exact Or.inr (Or.inl ⟨hp, ho, hv⟩)
    · rw [← hp, s.matchingProcessed_next_iff ht hnext] at hm
      rcases hm with hm | hm
      · exact Or.inl (Or.inr ⟨ho, hp, hp ▸ hm⟩)
      · exact Or.inr (Or.inr ⟨ho, hp, hp ▸ hm⟩)
  · rintro ((⟨hp, ho, hv⟩ | ⟨ho, hp, hm⟩) | ⟨hp, ho, hv⟩ | ⟨ho, hp, hm⟩)
    · exact Or.inl ⟨hp, ho, (s.visited_next_iff hnext a.2).mpr (Or.inl hv)⟩
    · refine Or.inr ⟨ho, hp, ?_⟩
      rw [← hp, s.matchingProcessed_next_iff ht hnext]
      exact Or.inl (hp ▸ hm)
    · exact Or.inl ⟨hp, ho, (s.visited_next_iff hnext a.2).mpr (Or.inr hv)⟩
    · refine Or.inr ⟨ho, hp, ?_⟩
      rw [← hp, s.matchingProcessed_next_iff ht hnext]
      exact Or.inr (hp ▸ hm)

/-- Internal source attachments at the new endpoint are precisely earlier inward
matching endpoints on the side being visited. -/
theorem Source.internalAdded_new_inward_iff {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (owner : Bool) (b : Point spec.n) :
    s.internalAdded t (s.newPoint hnext) (s.newPoint hnext)
      (inwardIncidence (Group.onSide owner side) b).2 ↔ b.val < t.processed side := by
  have hn := s.newPoint_not_visited hnext
  simp only [Source.internalAdded, hn, and_false, or_false, true_and]
  have hi := s.visit_lt hnext
  rw [s.sideLength_eq] at hi
  obtain ⟨hl, hr⟩ := ht
  have hb := b.isLt
  have hc := s.cut_le
  cases side <;> cases owner <;>
    simp only [Source.newPoint, sourcePoint, Group.onSide, inwardIncidence, Group.side,
      visited, Stage.processed, Bool.false_eq_true, ite_true, ite_false,
      Point.mirror_mirror, Point.mirror_val] at hi ⊢ <;> omega

/-- The original internal attachment event is exactly the original owner D
letter. Thus an original U adds no internal matching edge. -/
theorem Source.internalAdded_new_iff_D {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (owner : Bool) :
    s.internalAdded t (s.newPoint hnext) (s.newPoint hnext)
      ((ownerMatching s.matchings owner).partner (s.newPoint hnext)) ↔
        (s.word (Group.onSide owner side))[t.processed side]? = some DyckStep.D := by
  let g := Group.onSide owner side
  let p : Point spec.n := ⟨t.processed side, s.visit_lt_size hnext⟩
  have howner : g.upper = owner := by cases side <;> cases owner <;> rfl
  have hpoint : (inwardIncidence g p).2 = s.newPoint hnext := by
    cases side <;> cases owner <;> rfl
  have hpartner := s.inward_partner g p
  rw [howner, hpoint] at hpartner
  rw [← hpartner, s.internalAdded_new_inward_iff ht hnext]
  have hside : (Group.onSide owner side).side = side := by
    cases side <;> cases owner <;> rfl
  rw [s.word_inward, hside, List.getElem?_take_of_lt (s.visit_lt hnext)]
  change ((s.inwardMatching g).partner p).val < p.val ↔
    (s.inwardMatching g).wordOf[p.val]? = some DyckStep.D
  rw [source_step_D_iff]
  have hne := (s.inwardMatching g).partner_ne p
  have hv : ((s.inwardMatching g).partner p).val ≠ p.val := by
    intro he
    exact hne (Fin.ext he)
  simp only [NoncrossingMatching.opens, Fin.lt_def]
  omega

/-- For either owner, the native D bit agrees with its original source letter. -/
theorem Source.nextMove_ownerDown_iff {spec : RunSpec} (s : Source spec)
    (t : Stage) (side : Side) (owner : Bool) :
    (if owner then (s.nextMove t side).upperDown else (s.nextMove t side).lowerDown) = true ↔
      (s.word (Group.onSide owner side))[t.processed side]? = some DyckStep.D := by
  cases owner <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    s.nextMove_upperDown, s.nextMove_lowerDown, decide_eq_true_eq]

/-- An arbitrary original matching edge is an internal attachment exactly when
it touches the new point and the source label has D for its owner. -/
theorem Source.internalAdded_matching_iff {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (owner : Bool) (a b : Point spec.n)
    (hp : (ownerMatching s.matchings owner).partner a = b) :
    s.internalAdded t (s.newPoint hnext) a b ↔
      (if owner then (s.nextMove t side).upperDown else (s.nextMove t side).lowerDown) = true ∧
        (a = s.newPoint hnext ∨ b = s.newPoint hnext) := by
  rw [s.nextMove_ownerDown_iff]
  have hs (x y : Point spec.n) :
      s.internalAdded t (s.newPoint hnext) x y ↔
        s.internalAdded t (s.newPoint hnext) y x := by
    simp only [Source.internalAdded]
    tauto
  constructor
  · intro h
    have hend := h.2.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    refine ⟨?_, hend⟩
    rcases hend with rfl | rfl
    · rw [← hp] at h
      exact (s.internalAdded_new_iff_D ht hnext owner).mp h
    · have hm : (ownerMatching s.matchings owner).partner (s.newPoint hnext) = a := by
        rw [← hp, NoncrossingMatching.partner_partner]
      have hh := (hs _ _).mp h
      rw [← hm] at hh
      exact (s.internalAdded_new_iff_D ht hnext owner).mp hh
  · rintro ⟨hD, rfl | rfl⟩
    · rw [← hp]
      exact (s.internalAdded_new_iff_D ht hnext owner).mpr hD
    · have hm : (ownerMatching s.matchings owner).partner (s.newPoint hnext) = a := by
        rw [← hp, NoncrossingMatching.partner_partner]
      apply (hs _ _).mpr
      rw [← hm]
      exact (s.internalAdded_new_iff_D ht hnext owner).mpr hD

/-- Physical source edges added by one visit, before any path contractions. -/
def Source.visitEdges {spec : RunSpec} (s : Source spec) {t : Stage} {side : Side}
    (hnext : s.Progress (t.next side)) : SimpleGraph (Incidence spec.n) where
  Adj a b :=
    (a.2 = b.2 ∧ a.1 ≠ b.1 ∧ a.2 = s.newPoint hnext) ∨
    (a.1 = b.1 ∧ (ownerMatching s.matchings a.1).partner a.2 = b.2 ∧
      (s.internalAdded t (s.newPoint hnext) a.2 b.2 ∨
        s.throughAdded t side a.1 a.2 b.2))
  symm := ⟨by
    intro a b h
    rcases h with ⟨hp, ho, hn⟩ | ⟨ho, hp, he⟩
    · exact Or.inl ⟨hp.symm, ho.symm, hp ▸ hn⟩
    · refine Or.inr ⟨ho.symm, ?_, ?_⟩
      · rw [← ho, ← hp, NoncrossingMatching.partner_partner]
      · rw [← ho]
        rcases he with ⟨hs, he | he⟩ | he
        · exact Or.inl ⟨hs.symm, Or.inr he⟩
        · exact Or.inl ⟨hs.symm, Or.inl he⟩
        · exact Or.inr (he.elim Or.inr Or.inl)⟩
  loopless := ⟨by
    intro a h
    rcases h with ⟨_, hn, _⟩ | ⟨_, hp, _⟩
    · exact hn rfl
    · exact (ownerMatching s.matchings a.1).partner_ne a.2 hp⟩

/-- Exact graph equality for one source visit. The added graph contains the
new crossing, original D attachments, and the next per-owner FIFO through edge. -/
theorem Source.partialGraph_next {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side)) :
    s.partialGraph (t.next side) = s.partialGraph t ⊔ s.visitEdges hnext := by
  ext a b
  exact s.partialGraph_next_adj_iff ht hnext a b

/-- Every event edge is absent from the old partial graph. In particular, the
source update never re-adds an earlier matching edge. -/
theorem Source.visitEdges_not_old {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side))
    {a b : Incidence spec.n} (h : (s.visitEdges hnext).Adj a b) :
    ¬(s.partialGraph t).Adj a b := by
  have hn := s.newPoint_not_visited hnext
  rcases h with ⟨hp, ho, he⟩ | ⟨ho, hp, he⟩
  · rintro (⟨_, _, hv⟩ | ⟨ho', _, _⟩)
    · exact hn (he ▸ hv)
    · exact ho ho'
  · rintro (⟨_, ho', _⟩ | ⟨_, _, ha, hb, hs⟩)
    · exact ho' ho
    · rcases he with ⟨_, ⟨he, _⟩ | ⟨he, _⟩⟩ | he
      · exact hn (he ▸ ha)
      · exact hn (he ▸ hb)
      · simp only [Source.throughAdded] at he
        rcases hs with hs | hs
        · rcases he with ⟨hc, hd, _⟩ | ⟨hc, hd, _⟩ <;> omega
        · simp only [Source.joinedThrough] at hs
          rcases he with ⟨hc, hd, hlo, _⟩ | ⟨hc, hd, hlo, _⟩ <;>
            rcases hs with ⟨hc', hd', hh⟩ | ⟨hc', hd', hh⟩ <;> omega

/-- The concrete event graph is exactly the newly present edge set. This is a
derived characterization; the event graph itself uses physical source data. -/
theorem Source.visitEdges_iff_new {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (a b : Incidence spec.n) :
    (s.visitEdges hnext).Adj a b ↔
      (s.partialGraph (t.next side)).Adj a b ∧ ¬(s.partialGraph t).Adj a b := by
  rw [s.partialGraph_next ht hnext, SimpleGraph.sup_adj]
  constructor
  · intro h
    exact ⟨Or.inr h, s.visitEdges_not_old hnext h⟩
  · rintro ⟨h | h, hn⟩
    · exact False.elim (hn h)
    · exact h

end Meanders.FirstCrossing
