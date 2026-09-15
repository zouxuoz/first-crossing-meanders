import Meanders.Models.FirstCrossing.Interpretation.OpeningStep
import Meanders.Models.FirstCrossing.Interpretation.JoinedVisited
import Meanders.Models.FirstCrossing.Native.Codec

/-! Physical retained endpoints and boundary degrees for the shared source carrier. -/

namespace Meanders.FirstCrossing

open SimpleGraph

/-- Interpret an inward point as its physical owner incidence. -/
def inwardIncidence {n : Nat} (g : Group) (a : Point n) : Incidence n :=
  (g.upper, match g.side with | .left => a | .right => a.mirror)

theorem Source.progress_le_boundary {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) : t.processed g.side ≤ 2 * spec.n := by
  have hc := s.cut_le
  obtain ⟨hl, hr⟩ := ht
  cases g <;> simp only [Group.side, Stage.processed] <;> omega

/-- The independent old-opening index list is precisely the physical source
stack after deleting the already joined oldest ordinals. -/
theorem Source.retainedIndices_eq_map {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) :
    s.retainedIndices t g =
      ((sourceOpeningList (s.inwardMatching g) (t.processed g.side)).drop (s.joined t g)).map
        Fin.val := by
  rw [Source.retainedIndices, Source.openingIndices, s.prefix_inward ht,
    ← sourceOpeningList_map _ (s.progress_le_boundary ht g), ← List.map_drop]

theorem inwardIncidence_injective {n : Nat} (g : Group) :
    Function.Injective (inwardIncidence (n := n) g) := by
  intro a b he
  have hp := congrArg Prod.snd he
  cases g <;> simp only [inwardIncidence, Group.side] at hp
  · exact hp
  · exact Point.mirror_injective hp
  · exact hp
  · exact Point.mirror_injective hp

/-- Physical incidence membership remembers the original inward index. -/
theorem Source.mem_retainedGroup_iff_index {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) (a : Point spec.n) :
    inwardIncidence g a ∈ s.retainedGroup ht g ↔ a.val ∈ s.retainedIndices t g := by
  constructor
  · intro h
    obtain ⟨⟨i, hi⟩, _, he⟩ := List.mem_map.mp h
    have he' : inwardIncidence g (⟨i, s.retainedIndex_lt ht g hi⟩ : Point spec.n) =
        inwardIncidence g a := by
      exact he
    have hi' := congrArg Fin.val (inwardIncidence_injective g he')
    exact hi' ▸ hi
  · intro hi
    apply List.mem_map.mpr
    refine ⟨⟨a.val, hi⟩, List.mem_attach _ _, ?_⟩
    cases g <;> rfl

/-- Original active openings are retained exactly from the first unjoined
ordinal onward; no quotient or renumbering occurs. -/
theorem Source.mem_retainedGroup_iff {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) (a : Point spec.n) :
    inwardIncidence g a ∈ s.retainedGroup ht g ↔
      a ∈ (s.inwardMatching g).active (t.processed g.side) ∧
        s.joined t g ≤
          (((s.inwardMatching g).active (t.processed g.side)).filter (· < a)).card := by
  rw [s.mem_retainedGroup_iff_index ht, Source.retainedIndices, Source.openingIndices,
    s.prefix_inward ht, sourceOpeningNat_mem_drop _ (s.progress_le_boundary ht g)]

/-- The two scans visit disjoint physical halves; an inward point inside its
half is visited exactly when its original side counter passes it. -/
theorem Source.visited_inward_iff {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) (a : Point spec.n)
    (ha : a.val < spec.sideLength g.side) :
    visited t (inwardIncidence g a).2 ↔ a.val < t.processed g.side := by
  rw [s.sideLength_eq] at ha
  have hcut := s.cut_le
  have hsize := a.isLt
  obtain ⟨hl, hr⟩ := ht
  cases g <;>
    simp only [inwardIncidence, Group.side, visited, Point.mirror_mirror, Point.mirror_val,
      Stage.processed] at ha ⊢ <;> omega

theorem Source.inward_partner {spec : RunSpec} (s : Source spec) (g : Group)
    (a : Point spec.n) :
    (inwardIncidence g ((s.inwardMatching g).partner a)).2 =
      (ownerMatching s.matchings g.upper).partner (inwardIncidence g a).2 := by
  cases g <;> simp [inwardIncidence, Source.inwardMatching, Group.side,
    NoncrossingMatching.partner_reflect]

/-- Before classifying ports, joined-through events already imply both physical
endpoints have been visited; no extra visibility hypothesis is needed. -/
theorem Source.matchingProcessed_iff {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (owner : Bool) (a : Point spec.n) :
    s.matchingProcessed t owner a ((ownerMatching s.matchings owner).partner a) ↔
      (visited t a ∧ visited t ((ownerMatching s.matchings owner).partner a) ∧
        (a.val < s.cut ↔ ((ownerMatching s.matchings owner).partner a).val < s.cut)) ∨
      s.joinedThrough t owner a ((ownerMatching s.matchings owner).partner a) := by
  constructor
  · rintro ⟨ha, hb, hside | hj⟩
    · exact Or.inl ⟨ha, hb, hside⟩
    · exact Or.inr hj
  · rintro (⟨ha, hb, hside⟩ | hj)
    · exact ⟨ha, hb, Or.inl hside⟩
    · have hv := s.joinedThrough_visited ht owner rfl hj
      exact ⟨hv.1, hv.2, Or.inr hj⟩

private theorem Source.visited_same_half_iff {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) (a b : Point spec.n)
    (ha : a.val < spec.sideLength g.side) :
    (visited t (inwardIncidence g b).2 ∧
      ((inwardIncidence g a).2.val < s.cut ↔ (inwardIncidence g b).2.val < s.cut)) ↔
      b.val < t.processed g.side := by
  rw [s.sideLength_eq] at ha
  have hcut := s.cut_le
  have hasize := a.isLt
  have hbsize := b.isLt
  obtain ⟨hl, hr⟩ := ht
  cases g <;>
    simp only [inwardIncidence, Group.side, visited, Point.mirror_mirror, Point.mirror_val,
      Stage.processed] at ha ⊢ <;> omega

/-- A physical degree-one incidence is an original active inward opening whose
through arch has not yet joined. This proof is shared by both sectors and sides. -/
theorem Source.degree_one_inward_iff {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) (a : Point spec.n)
    (ha : a.val < spec.sideLength g.side) :
    (s.partialGraph t).degree (inwardIncidence g a) = 1 ↔
      a ∈ (s.inwardMatching g).active (t.processed g.side) ∧
        ¬s.joinedThrough t g.upper (inwardIncidence g a).2
          ((ownerMatching s.matchings g.upper).partner (inwardIncidence g a).2) := by
  rw [s.partialGraph_degree_one_iff]
  change visited t (inwardIncidence g a).2 ∧
    ¬s.matchingProcessed t g.upper (inwardIncidence g a).2
      ((ownerMatching s.matchings g.upper).partner (inwardIncidence g a).2) ↔ _
  rw [s.matchingProcessed_iff ht]
  have hsame := s.visited_same_half_iff ht g a ((s.inwardMatching g).partner a) ha
  rw [s.inward_partner] at hsame
  rw [hsame, s.visited_inward_iff ht g a ha, NoncrossingMatching.mem_active]
  constructor
  · rintro ⟨hav, hn⟩
    exact ⟨⟨hav, Nat.le_of_not_gt (fun h => hn (Or.inl ⟨hav, h⟩))⟩,
      fun h => hn (Or.inr h)⟩
  · rintro ⟨⟨hav, hp⟩, hn⟩
    exact ⟨hav, fun h => h.elim (fun h => Nat.not_lt_of_ge hp h.2) hn⟩

/-- For an original active opening, the physical through-join test is precisely
the comparison with its original prefix ordinal. -/
theorem Source.joinedThrough_active_iff {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) (a : Point spec.n)
    (ha : a ∈ (s.inwardMatching g).active (t.processed g.side)) :
    s.joinedThrough t g.upper (inwardIncidence g a).2
        ((ownerMatching s.matchings g.upper).partner (inwardIncidence g a).2) ↔
      (((s.inwardMatching g).active (t.processed g.side)).filter (· < a)).card <
        s.joined t g := by
  have hprogress := s.progress_length ht g
  rw [s.word_length] at hprogress
  have hside : a.val < spec.sideLength g.side :=
    lt_of_lt_of_le ((s.inwardMatching g).mem_active.mp ha).1 hprogress
  have hpoint : (inwardIncidence g a).2 = sourcePoint g.side a.val a.isLt := by
    cases g <;> rfl
  have hj := s.joinedThrough_inward_iff t g a hside
  dsimp only at hj
  rw [hpoint, hj]
  have hold : a.val ∈ oldOpenings ((s.word g).take (t.processed g.side)) := by
    rw [s.prefix_inward ht]
    exact (oldOpenings_matching_prefix _ (s.progress_le_boundary ht g) a).mpr ha
  have hord :
      ((oldOpenings ((s.word g).take (t.processed g.side))).filter (· < a.val)).card =
        (((s.inwardMatching g).active (t.processed g.side)).filter (· < a)).card := by
    rw [s.prefix_inward ht, leftThrough_ordinal _ (s.progress_le_boundary ht g)]
  constructor
  · rintro ⟨hfull, hrank⟩
    have he := oldOpening_ordinal_append hold
      (by simpa only [List.take_append_drop] using hfull :
        a.val ∈ oldOpenings ((s.word g).take (t.processed g.side) ++
          (s.word g).drop (t.processed g.side)))
    rw [List.take_append_drop, hord] at he
    rwa [← he]
  · intro hrank
    have hemit :
        ((oldOpenings ((s.word g).take (t.processed g.side))).filter (· < a.val)).card <
          (geometry spec t (s.counters t)).emitted.get g := by
      rw [hord]
      exact hrank.trans_le (Nat.min_le_left _ _)
    obtain ⟨hfull, he⟩ := s.emitted_opening_survives ht g hold hemit
    exact ⟨hfull, by rwa [he, hord]⟩

/-- Retained source endpoints are exactly physical degree-one incidences within
their original half. This covers LOW, HIGH, both owners, and both scan directions. -/
theorem Source.mem_retainedGroup_iff_degree_one {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) (a : Point spec.n)
    (ha : a.val < spec.sideLength g.side) :
    inwardIncidence g a ∈ s.retainedGroup ht g ↔
      (s.partialGraph t).degree (inwardIncidence g a) = 1 := by
  rw [s.mem_retainedGroup_iff ht, s.degree_one_inward_iff ht g a ha]
  apply and_congr_right
  intro hactive
  rw [s.joinedThrough_active_iff ht g a hactive, not_lt]

theorem Source.retainedGroup_degree_one {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) {a : Incidence spec.n}
    (ha : a ∈ s.retainedGroup ht g) : (s.partialGraph t).degree a = 1 := by
  obtain ⟨⟨i, hi⟩, _, rfl⟩ := List.mem_map.mp ha
  let b : Point spec.n := ⟨i, s.retainedIndex_lt ht g hi⟩
  have hside : b.val < spec.sideLength g.side := by
    have hp := s.progress_length ht g
    rw [s.word_length] at hp
    exact lt_of_lt_of_le (s.retainedIndex_lt_processed t g hi) hp
  exact (s.mem_retainedGroup_iff_degree_one ht g b hside).mp
    ((s.mem_retainedGroup_iff_index ht g b).mpr hi)

/-- The shared carrier boundary is precisely the set of physical degree-one
incidences of the processed source graph. No source completion edges are added
to make this statement true. -/
theorem Source.mem_retainedBoundary_iff_degree_one {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (a : Incidence spec.n) :
    a ∈ s.retainedBoundary ht ↔ (s.partialGraph t).degree a = 1 := by
  constructor
  · intro ha
    simp only [Source.retainedBoundary, List.mem_append] at ha
    rcases ha with ((ha | ha) | ha) | ha
    · exact s.retainedGroup_degree_one ht .pl ha
    · exact s.retainedGroup_degree_one ht .pr ha
    · exact s.retainedGroup_degree_one ht .ql ha
    · exact s.retainedGroup_degree_one ht .qr ha
  · intro hd
    rcases a with ⟨owner, a⟩
    by_cases hleft : a.val < s.cut
    · let g := Group.onSide owner .left
      have hside : a.val < spec.sideLength g.side := by
        rw [s.sideLength_eq]
        cases owner <;> exact hleft
      have hp : inwardIncidence g a = (owner, a) := by cases owner <;> rfl
      have hm := (s.mem_retainedGroup_iff_degree_one ht g a hside).mpr (hp.symm ▸ hd)
      rw [hp] at hm
      simp only [Source.retainedBoundary, List.mem_append]
      cases owner
      · exact Or.inl (Or.inr hm)
      · exact Or.inl (Or.inl (Or.inl hm))
    · let g := Group.onSide owner .right
      have hside : a.mirror.val < spec.sideLength g.side := by
        rw [s.sideLength_eq]
        have hasize := a.isLt
        have hcut := s.cut_le
        cases owner <;>
          simp only [g, Group.onSide, Group.side, Point.mirror_val, Bool.false_eq_true,
            ite_false, ite_true] <;> omega
      have hp : inwardIncidence g a.mirror = (owner, a) := by
        cases owner <;> simp [inwardIncidence, g, Group.onSide, Group.side, Group.upper]
      have hm := (s.mem_retainedGroup_iff_degree_one ht g a.mirror hside).mpr (hp.symm ▸ hd)
      rw [hp] at hm
      simp only [Source.retainedBoundary, List.mem_append]
      cases owner
      · exact Or.inr hm
      · exact Or.inl (Or.inl (Or.inr hm))

end Meanders.FirstCrossing

/-!
# Unique physical boundary and raw key representation

Sorted original opening indices have no duplicates. Their physical images lie
in disjoint owner/side groups, so the retained boundary provides an injective
port naming. A valid mate array is then determined by the source reachability
relation in that fixed boundary order.
-/

namespace Meanders.FirstCrossing

/-- Original retained indices remain duplicate-free after dropping joined ordinals. -/
theorem Source.retainedIndices_nodup {spec : RunSpec} (s : Source spec)
    (t : Stage) (g : Group) : (s.retainedIndices t g).Nodup := by
  exact ((oldOpenings ((s.word g).take (t.processed g.side))).sort_nodup (· ≤ ·)).drop

/-- Each group's physical map preserves the uniqueness of its original positions. -/
theorem Source.retainedGroup_nodup {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) : (s.retainedGroup ht g).Nodup := by
  unfold Source.retainedGroup
  apply List.Nodup.map
  · intro i j he
    apply Subtype.ext
    have hp := congrArg Prod.snd he
    cases g <;> simp only [sourcePoint, Group.side] at hp
    · exact congrArg Fin.val hp
    · exact congrArg Fin.val (Point.mirror_injective hp)
    · exact congrArg Fin.val hp
    · exact congrArg Fin.val (Point.mirror_injective hp)
  · exact (s.retainedIndices_nodup t g).attach

/-- A retained incidence remembers its owner and lies strictly in its physical cut half. -/
theorem Source.retainedGroup_location {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) {a : Incidence spec.n}
    (ha : a ∈ s.retainedGroup ht g) :
    a.1 = g.upper ∧ (a.2.val < s.cut ↔ g.side = .left) := by
  obtain ⟨⟨i, hi⟩, _, rfl⟩ := List.mem_map.mp ha
  have hp := s.retainedIndex_lt_processed t g hi
  have hcut := s.cut_le
  obtain ⟨hl, hr⟩ := ht
  cases g <;>
    simp_all [sourcePoint, Group.side, Group.upper, Stage.processed] <;> omega

/-- Different owner/side groups have disjoint physical incidence images. -/
theorem Source.retainedGroup_disjoint {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) {g h : Group} (hne : g ≠ h) :
    List.Disjoint (s.retainedGroup ht g) (s.retainedGroup ht h) := by
  rw [List.disjoint_left]
  intro a ha hb
  have hga := s.retainedGroup_location ht g ha
  have hha := s.retainedGroup_location ht h hb
  cases g <;> cases h <;> simp_all [Group.upper, Group.side]

/-- The actual retained physical boundary supplies each port exactly once. -/
theorem Source.retainedBoundary_nodup {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) : (s.retainedBoundary ht).Nodup := by
  simp only [Source.retainedBoundary, List.nodup_append', List.disjoint_append_left]
  exact ⟨⟨⟨s.retainedGroup_nodup ht .pl, s.retainedGroup_nodup ht .pr,
      s.retainedGroup_disjoint ht (by decide)⟩,
    s.retainedGroup_nodup ht .ql, s.retainedGroup_disjoint ht (by decide),
      s.retainedGroup_disjoint ht (by decide)⟩,
    s.retainedGroup_nodup ht .qr, ⟨s.retainedGroup_disjoint ht (by decide),
      s.retainedGroup_disjoint ht (by decide)⟩, s.retainedGroup_disjoint ht (by decide)⟩

/-- A source graph in its fixed boundary order determines its raw key uniquely.
Validity of one mate array already supplies every distinct partner needed in the comparison. -/
theorem Source.RepresentsKey.unique {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x y : Key}
    (hx : s.RepresentsKey ht x) (hy : s.RepresentsKey ht y)
    (hpair : pairingValid x.mate = true) : x = y := by
  have hcounts : x.counters = y.counters := hx.1.trans hy.1.symm
  have hlength : x.mate.length = y.mate.length := hx.2.1.trans hy.2.1.symm
  have hmates : x.mate = y.mate := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < x.mate.length
    · obtain ⟨j, hij, hne, hji⟩ := (pairingValid_iff x.mate).mp hpair i hi
      have hj : j < x.mate.length := (List.getElem?_eq_some_iff.mp hji).1
      let I : Fin (s.retainedBoundary ht).length := ⟨i, by rw [← hx.2.1]; exact hi⟩
      let J : Fin (s.retainedBoundary ht).length := ⟨j, by rw [← hx.2.1]; exact hj⟩
      have hreach := (hx.2.2 I J).mpr (Or.inr hij)
      have htarget : y.mate[i]? = some j := by
        rcases (hy.2.2 I J).mp hreach with he | he
        · exact False.elim (hne (congrArg Fin.val he))
        · exact he
      exact hij.trans htarget.symm
    · have hxnone := List.getElem?_eq_none (Nat.le_of_not_gt hi)
      have hynone : y.mate[i]? = none := List.getElem?_eq_none (by omega)
      exact hxnone.trans hynone.symm
  cases x
  cases y
  exact congrArg₂ Key.mk hcounts hmates

end Meanders.FirstCrossing
