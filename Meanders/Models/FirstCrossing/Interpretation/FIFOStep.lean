import Meanders.Models.FirstCrossing.Interpretation.GraphStep

/-!
# Physical source endpoints at the FIFO drain

The temporary lists are the original post-visit opening lists with only the
previously joined prefix removed. Their heads, when a join is newly enabled,
are the original next through-arch endpoints.
-/

namespace Meanders.FirstCrossing

/-- Original post-visit openings before deleting any newly joined FIFO heads. -/
noncomputable def Source.beforeDrainIndices {spec : RunSpec} (s : Source spec)
    (t : Stage) (side : Side) (g : Group) : List Nat :=
  (s.openingIndices (t.next side) g).drop (s.joined t g)

/-- Physical owner/side endpoints after attachment and before this visit's drain. -/
def Source.beforeDrainGroup {spec : RunSpec} (s : Source spec)
    (t : Stage) (side : Side) (g : Group) : List (Incidence spec.n) :=
  ((sourceOpeningList (s.inwardMatching g) ((t.next side).processed g.side)).drop
    (s.joined t g)).map (inwardIncidence g)

/-- Natural post-attachment indices use the same original physical matching stack. -/
theorem Source.beforeDrainIndices_eq_map {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side)) (g : Group) :
    s.beforeDrainIndices t side g =
      ((sourceOpeningList (s.inwardMatching g) ((t.next side).processed g.side)).drop
        (s.joined t g)).map Fin.val := by
  rw [Source.beforeDrainIndices, Source.openingIndices, s.prefix_inward hnext,
    ← sourceOpeningList_map _ (s.progress_le_boundary hnext g), ← List.map_drop]

private theorem head_drop_iff_ordinal {α : Type*} [LinearOrder α]
    (xs : List α) (hs : xs.Pairwise (· < ·)) (a : α) (k : Nat) :
    (xs.drop k).head? = some a ↔ a ∈ xs ∧ (xs.filter (· < a)).length = k := by
  induction xs generalizing k with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    by_cases ha : a ∈ xs
    · have hxa := hhead a ha
      cases k with
      | zero => simp [ha, hxa, ne_of_lt hxa]
      | succ k =>
        rw [List.drop_succ_cons, ih htail k]
        simp [ha, hxa]
    · have hdrop : ∀ k, (xs.drop k).head? ≠ some a := by
        intro k he
        exact ha (List.mem_of_mem_drop (List.mem_of_head? he))
      have hget (k : Nat) : xs[k]? ≠ some a := by
        simpa only [List.head?_drop] using hdrop k
      by_cases hax : a = x
      · subst a
        have hf : xs.filter (· < x) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro y hy
          have hxy := hhead y hy
          simp only [decide_eq_true_eq]
          exact not_lt_of_ge hxy.le
        cases k <;> simp [hf, hget]
      · cases k <;> simp [ha, hax, Ne.symm hax, hget]

/-- An actual oldest-first opening stack exposes precisely its next original ordinal. -/
theorem sourceOpeningList_head_drop {n i k : Nat} (m : NoncrossingMatching n)
    (a : Point n) :
    ((sourceOpeningList m i).drop k).head? = some a ↔
      a ∈ m.active i ∧ ((m.active i).filter (· < a)).card = k := by
  classical
  have hn : (sourceOpeningList m i).Nodup := by
    simpa only [sourceOpeningList, List.nodup_reverse, NoncrossingMatching.activeList] using
      (m.active i).sort_nodup (· ≥ ·)
  have hp : (sourceOpeningList m i).Pairwise (· ≤ ·) := by
    simpa only [sourceOpeningList, List.pairwise_reverse, NoncrossingMatching.activeList] using
      (m.active i).pairwise_sort (· ≥ ·)
  have hstrict : (sourceOpeningList m i).Pairwise (· < ·) :=
    (hp.and hn).imp fun hh => lt_of_le_of_ne hh.1 hh.2
  have he : (sourceOpeningList m i).toFinset = m.active i := by
    ext b
    simp
  have hc : ((sourceOpeningList m i).filter (· < a)).length =
      ((m.active i).filter (· < a)).card := by
    rw [← List.toFinset_card_of_nodup (hn.filter _), List.toFinset_filter, he]
    simp only [decide_eq_true_eq]
  rw [head_drop_iff_ordinal _ hstrict a k, sourceOpeningList_mem, hc]

/-- A full source opening below the new emission bound occupies its unchanged
original ordinal in the post-visit opening stack. -/
theorem Source.beforeDrain_head_of_ordinal {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side)) (g : Group)
    (a : Point spec.n) (_ha : a.val < spec.sideLength g.side)
    (hold : a.val ∈ oldOpenings (s.word g))
    (hord : ((oldOpenings (s.word g)).filter (· < a.val)).card = s.joined t g)
    (hnew : s.joined t g < s.joined (t.next side) g) :
    (s.beforeDrainGroup t side g).head? = some (inwardIncidence g a) := by
  let m := s.inwardMatching g
  have hi := s.progress_length hnext g
  rw [s.word_length] at hi
  have hsize : spec.sideLength g.side ≤ 2 * spec.n := by
    rw [s.sideLength_eq]
    have hc := s.cut_le
    cases g.side <;> simp only <;> omega
  have hfull : a ∈ m.active (spec.sideLength g.side) := by
    rw [s.word_inward] at hold
    exact (oldOpenings_matching_prefix m hsize a).mp hold
  have hlt : a.val < (t.next side).processed g.side :=
    s.oldOpening_lt_processed_of_ordinal_lt_emitted hnext g hold
      (by rw [hord]; exact hnew.trans_le (Nat.min_le_left _ _))
  have hp : a ∈ m.active ((t.next side).processed g.side) :=
    m.mem_active.mpr ⟨hlt, hi.trans (m.mem_active.mp hfull).2⟩
  have hpold : a.val ∈ oldOpenings ((s.word g).take ((t.next side).processed g.side)) := by
    rw [s.prefix_inward hnext]
    exact (oldOpenings_matching_prefix m (hi.trans hsize) a).mpr hp
  have he := oldOpening_ordinal_append (suffix := (s.word g).drop
    ((t.next side).processed g.side)) hpold
    (by simpa only [List.take_append_drop] using hold)
  simp only [List.take_append_drop] at he
  rw [s.prefix_inward hnext, leftThrough_ordinal m (hi.trans hsize)] at he
  have hhead := (sourceOpeningList_head_drop m a).mpr ⟨hp, he.symm.trans hord⟩
  simpa only [Source.beforeDrainGroup, List.head?_map, Option.map_some] using
    congrArg (Option.map (inwardIncidence g)) hhead

/-- A newly joined original through edge was absent from the previous shared prefix. -/
theorem Source.throughAdded_iff_new_joined {spec : RunSpec} (s : Source spec)
    (t : Stage) (side : Side) (owner : Bool) (a b : Point spec.n) :
    s.throughAdded t side owner a b ↔
      s.joinedThrough (t.next side) owner a b ∧ ¬s.joinedThrough t owner a b := by
  simp only [Source.throughAdded, Source.joinedThrough]
  omega

/-- The inward endpoint of a newly joined through edge is exactly the oldest
post-attachment FIFO slot of that group. -/
theorem Source.throughAdded_inward_head {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side)) (g : Group)
    (a : Point spec.n) (ha : a.val < spec.sideLength g.side)
    (h : s.throughAdded t side g.upper (sourcePoint g.side a.val a.isLt)
      ((ownerMatching s.matchings g.upper).partner (sourcePoint g.side a.val a.isLt))) :
    (s.beforeDrainGroup t side g).head? = some (inwardIncidence g a) := by
  rw [s.throughAdded_iff_new_joined] at h
  have hn := s.joinedThrough_inward_iff (t.next side) g a ha
  have ho := s.joinedThrough_inward_iff t g a ha
  dsimp only at hn ho
  rw [hn, ho] at h
  have hdelta := s.joined_next_between t side g
  have hge : ¬((oldOpenings (s.word g)).filter (· < a.val)).card < s.joined t g :=
    fun hh => h.2 ⟨h.1.1, hh⟩
  have hord : ((oldOpenings (s.word g)).filter (· < a.val)).card = s.joined t g := by
    omega
  exact s.beforeDrain_head_of_ordinal hnext g a ha h.1.1 hord (by omega)

/-- Both physical endpoints of a newly joined source through arch are exactly
the two FIFO heads selected by the native per-owner drain. -/
theorem Source.throughAdded_heads {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side))
    (owner : Bool) (a b : Point spec.n)
    (hp : (ownerMatching s.matchings owner).partner a = b)
    (ha : a.val < s.cut) (hb : s.cut ≤ b.val)
    (h : s.throughAdded t side owner a b) :
    (s.beforeDrainGroup t side (Group.onSide owner .left)).head? = some (owner, a) ∧
      (s.beforeDrainGroup t side (Group.onSide owner .right)).head? = some (owner, b) := by
  have hleft := s.throughAdded_inward_head hnext (Group.onSide owner .left) a
    (by simpa only [show (Group.onSide owner .left).side = .left by cases owner <;> rfl,
      s.sideLength_eq] using ha)
  have har : b.mirror.val < spec.sideLength .right := by
    rw [s.sideLength_eq]
    have hbs := b.isLt
    simp only [Point.mirror_val]
    omega
  have hright := s.throughAdded_inward_head hnext (Group.onSide owner .right) b.mirror
    (by simpa only [show (Group.onSide owner .right).side = .right by cases owner <;> rfl]
      using har)
  have hp' : (ownerMatching s.matchings owner).partner b = a := by
    rw [← hp, NoncrossingMatching.partner_partner]
  have hsym : s.throughAdded t side owner b a := h.elim Or.inr Or.inl
  cases owner <;>
    simp only [Group.onSide, Bool.false_eq_true, ite_false, ite_true, Group.side,
      Group.upper, sourcePoint, Fin.eta, Point.mirror_mirror, inwardIncidence, hp, hp']
      at hleft hright ⊢ <;>
    exact ⟨hleft h, hright hsym⟩

/-- Conversely, when the shared prefix advances, its actual FIFO head is the
endpoint of a newly joined original through edge. -/
theorem Source.beforeDrain_head_throughAdded {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side)) (g : Group)
    (a : Point spec.n)
    (hhead : (s.beforeDrainGroup t side g).head? = some (inwardIncidence g a))
    (hnew : s.joined t g < s.joined (t.next side) g) :
    s.throughAdded t side g.upper (sourcePoint g.side a.val a.isLt)
      ((ownerMatching s.matchings g.upper).partner (sourcePoint g.side a.val a.isLt)) := by
  rw [Source.beforeDrainGroup, List.head?_map, Option.map_eq_some_iff] at hhead
  obtain ⟨b, hb, hba⟩ := hhead
  have he := inwardIncidence_injective g hba
  subst b
  obtain ⟨hactive, hord⟩ := (sourceOpeningList_head_drop (s.inwardMatching g) a).mp hb
  have hi := s.progress_length hnext g
  rw [s.word_length] at hi
  have hlt := ((s.inwardMatching g).mem_active.mp hactive).1
  have ha := hlt.trans_le hi
  have hp : a.val ∈ oldOpenings ((s.word g).take ((t.next side).processed g.side)) := by
    rw [s.prefix_inward hnext]
    exact (oldOpenings_matching_prefix _ (s.progress_le_boundary hnext g) a).mpr hactive
  have hpord : ((oldOpenings ((s.word g).take ((t.next side).processed g.side))).filter
      (· < a.val)).card = s.joined t g := by
    rw [s.prefix_inward hnext, leftThrough_ordinal _ (s.progress_le_boundary hnext g)]
    exact hord
  have hfull := s.emitted_opening_survives hnext g hp
    (by rw [hpord]; exact hnew.trans_le (Nat.min_le_left _ _))
  have hfullord := hfull.2.trans hpord
  rw [s.throughAdded_iff_new_joined]
  have hn := s.joinedThrough_inward_iff (t.next side) g a ha
  have ho := s.joinedThrough_inward_iff t g a ha
  dsimp only at hn ho
  rw [hn, ho, hfullord]
  exact ⟨⟨hfull.1, hnew⟩, fun h => (Nat.lt_irrefl _ h.2)⟩

/-- The shared emitted prefix fits in the original active-opening stack. -/
theorem Source.joined_le_openingIndices {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) :
    s.joined t g ≤ (s.openingIndices t g).length := by
  rw [s.openingIndices_length ht]
  cases hs : spec.sector with
  | low => cases g <;> simp [Source.joined, geometry, hs, Counters.zero, Counters.get]
  | high L u v =>
    simp only [Source.joined, geometry, hs, Counters.get_ofFn]
    omega

/-- Whenever a drain is newly enabled, its physical post-attachment group has a head. -/
theorem Source.beforeDrainGroup_nonempty {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side)) (g : Group)
    (hnew : s.joined t g < s.joined (t.next side) g) :
    s.beforeDrainGroup t side g ≠ [] := by
  have hj := hnew.trans_le (s.joined_le_openingIndices hnext g)
  have hlength := congrArg List.length (s.beforeDrainIndices_eq_map hnext g)
  simp only [Source.beforeDrainIndices, List.length_drop, List.length_map] at hlength
  intro he
  have hz := congrArg List.length he
  simp only [Source.beforeDrainGroup, List.length_map, List.length_drop, List.length_nil] at hz
  omega

/-- The two FIFO slots consumed by an enabled owner drain are original matching
partners, and their physical edge is exactly a newly joined source through edge. -/
theorem Source.drain_heads_source_edge {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side))
    (owner : Bool) (a b : Point spec.n)
    (hleft : (s.beforeDrainGroup t side (Group.onSide owner .left)).head? = some (owner, a))
    (hright : (s.beforeDrainGroup t side (Group.onSide owner .right)).head? = some (owner, b))
    (hnew : s.joined t (Group.onSide owner .left) <
      s.joined (t.next side) (Group.onSide owner .left)) :
    (ownerMatching s.matchings owner).partner a = b ∧ s.throughAdded t side owner a b := by
  have hleft' : (s.beforeDrainGroup t side (Group.onSide owner .left)).head? =
      some (inwardIncidence (Group.onSide owner .left) a) := by
    cases owner <;> exact hleft
  have hadded := s.beforeDrain_head_throughAdded hnext (Group.onSide owner .left) a hleft' hnew
  have hadded' : s.throughAdded t side owner a
      ((ownerMatching s.matchings owner).partner a) := by
    cases owner <;> exact hadded
  have ha : a.val < s.cut := by
    have hmem := List.mem_of_head? hleft'
    rw [Source.beforeDrainGroup, List.mem_map] at hmem
    obtain ⟨c, hc, he⟩ := hmem
    have he' := inwardIncidence_injective _ he
    subst c
    have hc' := List.mem_of_mem_drop hc
    rw [sourceOpeningList_mem] at hc'
    have hi := s.progress_length hnext (Group.onSide owner .left)
    rw [s.word_length, s.sideLength_eq] at hi
    have hlt := ((s.inwardMatching (Group.onSide owner .left)).mem_active.mp hc').1
    cases owner <;> exact hlt.trans_le hi
  have hb : s.cut ≤ ((ownerMatching s.matchings owner).partner a).val := by
    rcases hadded' with h | h
    · exact h.2.1
    · exact False.elim (Nat.not_le.mpr ha h.2.1)
  have hheads := s.throughAdded_heads hnext owner a _ rfl ha hb hadded'
  have he := hheads.2.symm.trans hright
  have hp : (ownerMatching s.matchings owner).partner a = b := by
    exact congrArg Prod.snd (Option.some.inj he)
  exact ⟨hp, hp ▸ hadded'⟩

end Meanders.FirstCrossing
