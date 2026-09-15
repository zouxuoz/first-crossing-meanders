import Meanders.Models.FirstCrossing.Interpretation.Invariant

/-!
# Joined through arches have already visited endpoints

The existence of each emitted prefix ordinal is proved from the original ballot
prefix. Its survival and unchanged full-word ordinal identify the corresponding
physical through arch without assuming any native boundary representation.
-/

namespace Meanders.FirstCrossing

/-- Full-word old opening ordinals uniquely identify their physical positions. -/
theorem BallotHalf.oldOpening_ordinal_injective {len H : ℕ} (a : BallotHalf len H)
    {l k : ℕ} (hl : l ∈ oldOpenings a.word) (hk : k ∈ oldOpenings a.word)
    (he : ((oldOpenings a.word).filter (· < l)).card =
      ((oldOpenings a.word).filter (· < k)).card) : l = k := by
  rw [a.oldOpening_ordinal hl, a.oldOpening_ordinal hk] at he
  have hnl := a.prefix_nonneg l
  have hnk := a.prefix_nonneg k
  rw [Dyck.height_take] at hnl hnk
  rcases lt_trichotomy l k with h | h | h
  · have := (oldOpenings_level_order hl hk).mpr h
    omega
  · exact h
  · have := (oldOpenings_level_order hk hl).mpr h
    omega

/-- Every globally emitted old opening is present in the original processed prefix. -/
theorem Source.oldOpening_lt_processed_of_ordinal_lt_emitted {spec : RunSpec}
    (s : Source spec) {t : Stage} (ht : s.Progress t) (g : Group) {l : ℕ}
    (hl : l ∈ oldOpenings (s.word g))
    (he : ((oldOpenings (s.word g)).filter (· < l)).card <
      (geometry spec t (s.counters t)).emitted.get g) : l < t.processed g.side := by
  let ordinal := ((oldOpenings (s.word g)).filter (· < l)).card
  have heh : (geometry spec t (s.counters t)).emitted.get g ≤
      (height (s.word g) (t.processed g.side)).toNat := by
    rw [s.prefix_height ht]
    cases hs : spec.sector <;> cases g <;>
      simp [geometry, hs, Counters.zero, Counters.get, Counters.ofFn]
  obtain ⟨k, hkl, hkU, hkn, hkh⟩ := (s.prefixBallot ht g).exists_oldOpening_level
    (j := ordinal) (lt_of_lt_of_le he heh)
  have hk : k ∈ oldOpenings ((s.word g).take (t.processed g.side)) :=
    mem_oldOpenings.mpr ⟨hkl, hkU, hkn⟩
  have hko : ((oldOpenings ((s.word g).take (t.processed g.side))).filter (· < k)).card =
      ordinal := by
    change ((oldOpenings (s.prefixBallot ht g).word).filter (· < k)).card = ordinal
    rw [(s.prefixBallot ht g).oldOpening_ordinal hk, hkh, Int.toNat_natCast]
  have hfull := s.emitted_opening_survives ht g hk (by rw [hko]; exact he)
  have hsame : k = l := (s.wholeBallot g).oldOpening_ordinal_injective hfull.1 hl
    (hfull.2.trans hko)
  rw [hsame] at hkl
  simpa only [Source.prefixBallot, List.length_take,
    Nat.min_eq_left (s.progress_length ht g)] using hkl

/-- A joined through arch has already visited both of its inward endpoints. -/
theorem Source.joinedThrough_endpoints_lt {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (owner : Bool) {a b : Point spec.n}
    (hpair : (ownerMatching s.matchings owner).partner a = b)
    (ha : a.val < s.cut) (hb : s.cut ≤ b.val)
    (hjoined : (((ownerMatching s.matchings owner).active s.cut).filter (· < a)).card <
      s.joined t (Group.onSide owner .left)) :
    a.val < t.left ∧ b.mirror.val < t.right := by
  let m := ownerMatching s.matchings owner
  have hactive : a ∈ m.active s.cut := m.mem_active.mpr ⟨ha, by rwa [hpair]⟩
  have hright : b ∈ (m.active s.cut).image m.partner :=
    Finset.mem_image.mpr ⟨a, hactive, hpair⟩
  have hother : (Group.onSide owner .left).other = Group.onSide owner .right := by
    cases owner <;> rfl
  have hleftEmit : ((m.active s.cut).filter (· < a)).card <
      (geometry spec t (s.counters t)).emitted.get (Group.onSide owner .left) :=
    lt_of_lt_of_le hjoined (Nat.min_le_left _ _)
  have hrightEmit : ((m.active s.cut).filter (· < a)).card <
      (geometry spec t (s.counters t)).emitted.get (Group.onSide owner .right) := by
    have h := lt_of_lt_of_le hjoined (Nat.min_le_right _ _)
    simpa only [hother] using h
  have haold : a.val ∈ oldOpenings (s.word (Group.onSide owner .left)) := by
    rw [s.word_left]
    exact (oldOpenings_matching_prefix m s.cut_le a).mpr hactive
  have hbold : b.mirror.val ∈ oldOpenings (s.word (Group.onSide owner .right)) := by
    rw [s.word_right, ← (reflected_cut_halves m s.cut_le).1]
    exact (oldOpenings_matching_prefix m.reflect (by have := s.cut_le; omega) b.mirror).mpr
      ((reflected_active_iff_rightThrough m s.cut_le b).mpr hright)
  have hal := s.oldOpening_lt_processed_of_ordinal_lt_emitted ht
    (Group.onSide owner .left) haold (by
      rw [s.word_left, leftThrough_ordinal m s.cut_le]
      exact hleftEmit)
  have hbr := s.oldOpening_lt_processed_of_ordinal_lt_emitted ht
    (Group.onSide owner .right) hbold (by
      rw [s.word_right, rightThrough_ordinal m s.cut_le]
      have ho := through_pair_ordinal m hactive
      rw [hpair] at ho
      rw [← ho]
      exact hrightEmit)
  cases owner <;> exact ⟨hal, hbr⟩

/-- The symmetric through-edge predicate never inserts an edge with an unvisited endpoint. -/
theorem Source.joinedThrough_visited {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (owner : Bool) {a b : Point spec.n}
    (hpair : (ownerMatching s.matchings owner).partner a = b)
    (hjoined : s.joinedThrough t owner a b) : visited t a ∧ visited t b := by
  rcases hjoined with h | h
  · have hv := s.joinedThrough_endpoints_lt ht owner hpair h.1 h.2.1 h.2.2
    exact ⟨Or.inl hv.1, Or.inr hv.2⟩
  · have hpair' : (ownerMatching s.matchings owner).partner b = a := by
      rw [← hpair, NoncrossingMatching.partner_partner]
    have hv := s.joinedThrough_endpoints_lt ht owner hpair' h.1 h.2.1 h.2.2
    exact ⟨Or.inr hv.2, Or.inl hv.1⟩

/-- The two sides of one owner have the same number of completed FIFO joins. -/
theorem Source.joined_onSide_right {spec : RunSpec} (s : Source spec)
    (t : Stage) (owner : Bool) :
    s.joined t (Group.onSide owner .right) = s.joined t (Group.onSide owner .left) := by
  cases owner <;> dsimp only [Source.joined, Group.onSide, Group.other] <;>
    exact Nat.min_comm _ _

/-- The left inward full-word ordinal is the physical through-edge test. -/
theorem Source.joinedThrough_left_iff {spec : RunSpec} (s : Source spec)
    (t : Stage) (owner : Bool) (a : Point spec.n) (ha : a.val < s.cut) :
    s.joinedThrough t owner a ((ownerMatching s.matchings owner).partner a) ↔
      a.val ∈ oldOpenings (s.word (Group.onSide owner .left)) ∧
        ((oldOpenings (s.word (Group.onSide owner .left))).filter (· < a.val)).card <
          s.joined t (Group.onSide owner .left) := by
  rw [s.word_left, oldOpenings_matching_prefix _ s.cut_le,
    leftThrough_ordinal _ s.cut_le]
  simp only [Source.joinedThrough, NoncrossingMatching.mem_active, ha, true_and,
    show ¬ s.cut ≤ a.val from Nat.not_le.mpr ha, and_false, false_and, or_false]

/-- The right inward full-word ordinal is the same symmetric physical edge test. -/
theorem Source.joinedThrough_right_iff {spec : RunSpec} (s : Source spec)
    (t : Stage) (owner : Bool) (b : Point spec.n) (hb : s.cut ≤ b.val) :
    s.joinedThrough t owner b ((ownerMatching s.matchings owner).partner b) ↔
      b.mirror.val ∈ oldOpenings (s.word (Group.onSide owner .right)) ∧
        ((oldOpenings (s.word (Group.onSide owner .right))).filter
          (· < b.mirror.val)).card < s.joined t (Group.onSide owner .right) := by
  let m := ownerMatching s.matchings owner
  have hmem : b ∈ (m.active s.cut).image m.partner ↔ m.partner b ∈ m.active s.cut := by
    constructor
    · intro hb
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hb
      have he : m.partner b = a := by rw [← hab, m.partner_partner]
      rwa [he]
    · intro ha
      exact Finset.mem_image.mpr ⟨m.partner b, ha, m.partner_partner b⟩
  have hword : b.mirror.val ∈ oldOpenings (s.word (Group.onSide owner .right)) ↔
      m.partner b ∈ m.active s.cut := by
    rw [s.word_right, ← (reflected_cut_halves m s.cut_le).1,
      oldOpenings_matching_prefix m.reflect (by have := s.cut_le; omega),
      reflected_active_iff_rightThrough m s.cut_le, hmem]
  rw [hword, s.word_right, rightThrough_ordinal m s.cut_le, s.joined_onSide_right]
  constructor
  · intro hj
    have hactive : m.partner b ∈ m.active s.cut := by
      rcases hj with hj | hj
      · exact False.elim (Nat.not_lt.mpr hb hj.1)
      · exact m.mem_active.mpr ⟨hj.1, by simpa only [m.partner_partner] using hb⟩
    have hordinal := through_pair_ordinal m hactive
    rw [m.partner_partner] at hordinal
    refine ⟨hactive, ?_⟩
    rw [← hordinal]
    rcases hj with hj | hj
    · exact False.elim (Nat.not_lt.mpr hb hj.1)
    · exact hj.2.2
  · rintro ⟨hactive, hj⟩
    have hordinal := through_pair_ordinal m hactive
    rw [m.partner_partner] at hordinal
    rw [← hordinal] at hj
    exact Or.inr ⟨(m.mem_active.mp hactive).1, hb, hj⟩

/-- Each full inward old-opening ordinal describes exactly the physical joined-through test. -/
theorem Source.joinedThrough_inward_iff {spec : RunSpec} (s : Source spec)
    (t : Stage) (g : Group) (a : Point spec.n)
    (ha : a.val < spec.sideLength g.side) :
    let physical := sourcePoint g.side a.val a.isLt
    s.joinedThrough t g.upper physical ((ownerMatching s.matchings g.upper).partner physical) ↔
      a.val ∈ oldOpenings (s.word g) ∧
        ((oldOpenings (s.word g)).filter (· < a.val)).card < s.joined t g := by
  have hlen := s.sideLength_eq g.side
  rw [hlen] at ha
  cases g with
  | pl => exact s.joinedThrough_left_iff t true a ha
  | ql => exact s.joinedThrough_left_iff t false a ha
  | pr =>
    have hb : s.cut ≤ a.mirror.val := by
      have hn := a.isLt
      simp only [Group.side, Point.mirror_val] at ha ⊢
      omega
    simpa [sourcePoint, Group.side, Group.upper, Group.onSide] using
      s.joinedThrough_right_iff t true a.mirror hb
  | qr =>
    have hb : s.cut ≤ a.mirror.val := by
      have hn := a.isLt
      simp only [Group.side, Point.mirror_val] at ha ⊢
      omega
    simpa [sourcePoint, Group.side, Group.upper, Group.onSide] using
      s.joinedThrough_right_iff t false a.mirror hb

end Meanders.FirstCrossing
