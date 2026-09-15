import Meanders.Models.FirstCrossing.Original.ForcedPrefix
import Meanders.Models.FirstCrossing.Original.Exterior
import Meanders.Models.FirstCrossing.Native.State

/-!
# Original counters and source FIFO ordinals

These lemmas concern actual source words and physical matching endpoints.
They do not assume that the native retained-port pairing already represents
those endpoints; establishing that invariant remains a separate obligation.
-/

namespace Meanders.FirstCrossing

private theorem rightOrdinal_lt {α : Type*} [LinearOrder α] (s : Finset α)
    {a b : α} (hb : b ∈ s) (hab : a < b) :
    (s.filter (b < ·)).card < (s.filter (a < ·)).card := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hxs, hbx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxs, hab.trans hbx⟩
  · intro he
    have hmem : b ∈ s.filter (a < ·) := Finset.mem_filter.mpr ⟨hb, hab⟩
    rw [← he] at hmem
    exact lt_irrefl _ (Finset.mem_filter.mp hmem).2

/-- Equal oldest-first inward ordinals identify the actual through-arch partner. -/
theorem throughOrdinal_partner {n cut : ℕ} (m : NoncrossingMatching n) {a b : Point n}
    (ha : a ∈ m.active cut) (hb : b ∈ (m.active cut).image m.partner)
    (hordinal : ((m.active cut).filter (· < a)).card =
      (((m.active cut).image m.partner).filter (b < ·)).card) :
    m.partner a = b := by
  have hp : m.partner a ∈ (m.active cut).image m.partner := Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have he := through_pair_ordinal m ha
  rcases lt_trichotomy (m.partner a) b with h | h | h
  · have := rightOrdinal_lt ((m.active cut).image m.partner) hb h
    omega
  · exact h
  · have := rightOrdinal_lt ((m.active cut).image m.partner) hp h
    omega

/-- Each decoded native height is the original source-word prefix height. -/
theorem firstHeightCounters {s : RunSpec} {t : Stage} {c : Counters}
    (words : Group → List DyckStep)
    (hlen : ∀ g, t.processed g.side ≤ (words g).length)
    (hcount : ∀ g, c.get g = downs (words g) (t.processed g.side))
    (hnonneg : ∀ g, 0 ≤ height (words g) (t.processed g.side)) (g : Group) :
    ((geometry s t c).height.get g : ℤ) = height (words g) (t.processed g.side) := by
  have hh := height_eq_original_downs (words g) (t.processed g.side) (hlen g)
  rw [← hcount g] at hh
  have hn := hnonneg g
  have hg : (geometry s t c).height.get g = t.processed g.side - 2 * c.get g := by
    cases hs : s.sector <;> simp [geometry, hs]
  rw [hg]
  omega

/-- The actual unread part of a complete ballot half is a feasible suffix. -/
def BallotHalf.completionSuffix {i h len H : ℕ} (p : BallotHalf i h)
    (a : BallotHalf len H) (_hi : i ≤ len) (hp : p.word = a.word.take i) :
    BudgetSuffix h (len - i) (a.word.count DyckStep.D - p.word.count DyckStep.D) where
  word := a.word.drop i
  length_word := by simp [a.length_word]
  count_down := by
    have he : p.word.count DyckStep.D + (a.word.drop i).count DyckStep.D =
        a.word.count DyckStep.D := by
      rw [hp, ← List.count_append, List.take_append_drop]
    omega
  prefix_nonneg k := by
    have hsplit : a.word = p.word ++ a.word.drop i := by rw [hp, List.take_append_drop]
    have hk := a.prefix_nonneg (i + k)
    rw [Dyck.height_take, hsplit] at hk
    rw [show i + k = p.word.length + k by rw [p.length_word], height_append_right] at hk
    change 0 ≤ Dyck.height p.word + height (a.word.drop i) k at hk
    simpa only [p.height_word, Dyck.height_take] using hk

/-- Every forced physical prefix opening remains through-going in an actual completion. -/
theorem BallotHalf.forcedOpening_mem_completion {i h len H l : ℕ} (p : BallotHalf i h)
    (a : BallotHalf len H) (hi : i ≤ len) (hp : p.word = a.word.take i)
    (hl : l ∈ forcedOpenings p (a.word.count DyckStep.D) (len - i)) :
    l ∈ oldOpenings a.word := by
  classical
  obtain ⟨hlp, hall⟩ := Finset.mem_filter.mp hl
  obtain ⟨hll, hlU, hln⟩ := mem_oldOpenings.mp hlp
  have hsplit : a.word = p.word ++ a.word.drop i := by rw [hp, List.take_append_drop]
  have hnone := hall (p.completionSuffix a hi hp)
  change ¬ ∃ r, Paired (p.word ++ a.word.drop i) l r at hnone
  rw [← hsplit] at hnone
  apply mem_oldOpenings.mpr
  refine ⟨?_, ?_, hnone⟩
  · rw [hsplit, List.length_append]
    omega
  · rw [hsplit]
    simpa [List.getElem?_append, hll] using hlU

/-- A surviving prefix opening retains its original chronological ordinal.
In particular, forgetting previously joined ports cannot renumber future FIFO joins. -/
theorem oldOpening_ordinal_append {w suffix : List DyckStep} {l : ℕ}
    (hl : l ∈ oldOpenings w) (hlfull : l ∈ oldOpenings (w ++ suffix)) :
    ((oldOpenings (w ++ suffix)).filter (· < l)).card =
      ((oldOpenings w).filter (· < l)).card := by
  classical
  congr 1
  ext k
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hkfull, hkl⟩
    obtain ⟨hfull, hkU, hkn⟩ := mem_oldOpenings.mp hkfull
    have hll := (mem_oldOpenings.mp hl).1
    have hkw : k < w.length := by omega
    refine ⟨mem_oldOpenings.mpr ⟨hkw, ?_, ?_⟩, hkl⟩
    · simpa [List.getElem?_append, hkw] using hkU
    · rintro ⟨r, hr⟩
      exact hkn ⟨r, (paired_append_left hr.lt_length).mpr hr⟩
  · rintro ⟨hkw, hkl⟩
    have hkm := mem_oldOpenings.mp hkw
    have hlm := mem_oldOpenings.mp hl
    have hlfm := mem_oldOpenings.mp hlfull
    have hlevel := (oldOpenings_level_order hkw hl).mpr hkl
    refine ⟨mem_oldOpenings.mpr ⟨?_, ?_, ?_⟩, hkl⟩
    · simp only [List.length_append]; omega
    · simpa [List.getElem?_append, hkm.1] using hkm.2.1
    · apply (opening_unpaired_iff_above
        (by simp only [List.length_append]; omega : k < (w ++ suffix).length)
        (by simpa [List.getElem?_append, hkm.1] using hkm.2.1)).mpr
      intro q hkq hq
      by_cases hqw : q ≤ w.length
      · rw [height_append_left hkm.1.le, height_append_left hqw]
        exact (opening_unpaired_iff_above hkm.1 hkm.2.1).mp hkm.2.2 q hkq hqw
      · have hh := (opening_unpaired_iff_above hlfm.1 hlfm.2.1).mp hlfm.2.2 q
          (by omega) hq
        rw [height_append_left hkm.1.le]
        rw [height_append_left hlm.1.le] at hh
        exact hlevel.trans hh

/-- Emission preserves the global oldest-first ordinal in every complete ballot half. -/
theorem BallotHalf.forcedOpening_completion_ordinal {i h len H l : ℕ} (p : BallotHalf i h)
    (a : BallotHalf len H) (hi : i ≤ len) (hp : p.word = a.word.take i)
    (hl : l ∈ forcedOpenings p (a.word.count DyckStep.D) (len - i)) :
    ((oldOpenings a.word).filter (· < l)).card =
      ((oldOpenings p.word).filter (· < l)).card := by
  classical
  have hlp := (Finset.mem_filter.mp hl).1
  have hla := p.forcedOpening_mem_completion a hi hp hl
  have hsplit : a.word = p.word ++ a.word.drop i := by rw [hp, List.take_append_drop]
  rw [hsplit] at hla ⊢
  exact oldOpening_ordinal_append hlp hla

/-- Unmatched openings of a physical matching prefix are its actual through arches. -/
theorem oldOpenings_matching_prefix {n cut : ℕ} (m : NoncrossingMatching n)
    (hc : cut ≤ 2 * n) (a : Point n) :
    a.val ∈ oldOpenings (m.wordOf.take cut) ↔ a ∈ m.active cut := by
  have hsplit : m.wordOf.take cut ++ m.wordOf.drop cut = m.wordOf :=
    List.take_append_drop cut m.wordOf
  constructor
  · intro ha
    obtain ⟨hal, haU, han⟩ := mem_oldOpenings.mp ha
    have hac : a.val < cut := by simpa [List.length_take, Nat.min_eq_left hc] using hal
    have hU : m.wordOf[a.val]? = some DyckStep.U := by
      simpa [List.getElem?_take, hac] using haU
    have hop : a < m.partner a := by
      rw [m.getElem?_wordOf a.isLt, m.partnerIndex_coe] at hU
      split at hU
      · assumption
      · contradiction
    have hp := m.paired_wordOf (m.mk_mem_arches hop rfl)
    change Paired m.wordOf a.val (m.partner a).val at hp
    have hpartner : cut ≤ (m.partner a).val := by
      by_contra h
      have hb : (m.partner a).val < (m.wordOf.take cut).length := by
        simp [List.length_take, Nat.min_eq_left hc]
        omega
      have hpair : Paired (m.wordOf.take cut) a.val (m.partner a).val :=
        (paired_append_left hb).mp (hsplit.symm ▸ hp)
      exact han ⟨_, hpair⟩
    exact m.mem_active.mpr ⟨hac, hpartner⟩
  · intro ha
    obtain ⟨hac, hpartner⟩ := m.mem_active.mp ha
    have hop : a < m.partner a :=
      show a.val < (m.partner a).val from lt_of_lt_of_le hac hpartner
    have hp := m.paired_wordOf (m.mk_mem_arches hop rfl)
    change Paired m.wordOf a.val (m.partner a).val at hp
    apply mem_oldOpenings.mpr
    refine ⟨by simpa [List.length_take, Nat.min_eq_left hc] using hac, ?_, ?_⟩
    · simpa only [List.getElem?_take, ite_eq_left hac] using hp.isU
    · rintro ⟨r, hr⟩
      have hpair : Paired m.wordOf a.val r := hsplit ▸ (paired_append_left hr.lt_length).mpr hr
      have he := hp.right_unique hpair
      have hrl := hr.lt_length
      simp only [List.length_take, m.length_wordOf, Nat.min_eq_left hc] at hrl
      omega

/-- The physical left through ordinal is the oldest-first ordinal of the inward word. -/
theorem leftThrough_ordinal {n cut : ℕ} (m : NoncrossingMatching n) (hc : cut ≤ 2 * n)
    (a : Point n) :
    ((oldOpenings (m.wordOf.take cut)).filter (· < a.val)).card =
      ((m.active cut).filter (· < a)).card := by
  classical
  have he : (oldOpenings (m.wordOf.take cut)).filter (· < a.val) =
      ((m.active cut).filter (· < a)).image Fin.val := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hl, hla⟩
      have hln : l < 2 * n := by have := a.isLt; omega
      let b : Point n := ⟨l, hln⟩
      have hb : b ∈ m.active cut := (oldOpenings_matching_prefix m hc b).mp hl
      exact ⟨b, ⟨hb, hla⟩, rfl⟩
    · rintro ⟨b, ⟨hb, hba⟩, rfl⟩
      exact ⟨(oldOpenings_matching_prefix m hc b).mpr hb, hba⟩
  rw [he, Finset.card_image_of_injective]
  exact Fin.val_injective

/-- A reflected left-through opener is the mirrored physical right-through endpoint. -/
theorem reflected_active_iff_rightThrough {n cut : ℕ} (m : NoncrossingMatching n)
    (hc : cut ≤ 2 * n) (b : Point n) :
    b.mirror ∈ m.reflect.active (2 * n - cut) ↔ b ∈ (m.active cut).image m.partner := by
  have hb := b.isLt
  have hpb := (m.partner b).isLt
  constructor
  · intro h
    rw [NoncrossingMatching.mem_active, NoncrossingMatching.partner_reflect,
      Point.mirror_mirror, Point.mirror_val, Point.mirror_val] at h
    refine Finset.mem_image.mpr ⟨m.partner b, ?_, m.partner_partner b⟩
    rw [m.mem_active, m.partner_partner]
    constructor <;> omega
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    have ham := m.mem_active.mp ha
    rw [NoncrossingMatching.mem_active, NoncrossingMatching.partner_reflect,
      Point.mirror_mirror, m.partner_partner, Point.mirror_val, Point.mirror_val]
    have haL := a.isLt
    constructor <;> omega

/-- The right inward word's oldest-first ordinal is the decreasing physical ordinal. -/
theorem rightThrough_ordinal {n cut : ℕ} (m : NoncrossingMatching n) (hc : cut ≤ 2 * n)
    (b : Point n) :
    ((oldOpenings (Dyck.reverseComplement (m.wordOf.drop cut))).filter
      (· < b.mirror.val)).card =
      (((m.active cut).image m.partner).filter (b < ·)).card := by
  classical
  rw [← (reflected_cut_halves m hc).1, leftThrough_ordinal m.reflect (by omega)]
  have he : ((m.reflect.active (2 * n - cut)).filter (· < b.mirror)).image Point.mirror =
      ((m.active cut).image m.partner).filter (b < ·) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨x, ⟨hx, hxb⟩, rfl⟩
      have hright := (reflected_active_iff_rightThrough m hc x.mirror).mp (by simpa using hx)
      refine ⟨Finset.mem_image.mp hright, ?_⟩
      have hr := Point.mirror_lt_mirror.mpr hxb
      simpa using hr
    · rintro ⟨hy, hby⟩
      refine ⟨y.mirror, ⟨?_, Point.mirror_lt_mirror.mpr hby⟩, Point.mirror_mirror y⟩
      exact (reflected_active_iff_rightThrough m hc y).mpr (Finset.mem_image.mpr hy)
  rw [← he, Finset.card_image_of_injective]
  exact Point.mirror_injective

/-- Equal full inward-word ordinals identify the physical source arch itself. -/
theorem inwardFIFO_sound {n cut : ℕ} (m : NoncrossingMatching n) (hc : cut ≤ 2 * n)
    {a b : Point n} (ha : a.val ∈ oldOpenings (m.wordOf.take cut))
    (hb : b.mirror.val ∈ oldOpenings (Dyck.reverseComplement (m.wordOf.drop cut)))
    (he : ((oldOpenings (m.wordOf.take cut)).filter (· < a.val)).card =
      ((oldOpenings (Dyck.reverseComplement (m.wordOf.drop cut))).filter
        (· < b.mirror.val)).card) : m.partner a = b := by
  have hpa := (oldOpenings_matching_prefix m hc a).mp ha
  have hbr : b.mirror ∈ m.reflect.active (2 * n - cut) := by
    apply (oldOpenings_matching_prefix m.reflect (by omega) b.mirror).mp
    rwa [(reflected_cut_halves m hc).1]
  have hpb := (reflected_active_iff_rightThrough m hc b).mp hbr
  rw [leftThrough_ordinal m hc a, rightThrough_ordinal m hc b] at he
  exact throughOrdinal_partner m hpa hpb he

/-- Forced openings with equal emitted ordinals are partners in every full source.
Budgets are the original half lengths and cut height, never retained-port counts. -/
theorem forcedFIFO_source_sound {n cut H iL hL iR hR : ℕ}
    (m : MatchingAtCut n cut H) (hc : cut ≤ 2 * n)
    (pL : BallotHalf iL hL) (pR : BallotHalf iR hR)
    (hiL : iL ≤ cut) (hiR : iR ≤ 2 * n - cut)
    (hpreL : pL.word = (leftHalf hc m).word.take iL)
    (hpreR : pR.word = (rightHalf hc m).word.take iR)
    {a b : Point n}
    (hemitL : a.val ∈ forcedOpenings pL ((cut - H) / 2) (cut - iL))
    (hemitR : b.mirror.val ∈
      forcedOpenings pR ((2 * n - cut - H) / 2) (2 * n - cut - iR))
    (hordinal : ((oldOpenings pL.word).filter (· < a.val)).card =
      ((oldOpenings pR.word).filter (· < b.mirror.val)).card) :
    m.val.partner a = b := by
  have hL : a.val ∈
      forcedOpenings pL ((leftHalf hc m).word.count DyckStep.D) (cut - iL) := by
    rwa [(leftHalf hc m).down_budget]
  have hR : b.mirror.val ∈ forcedOpenings pR
      ((rightHalf hc m).word.count DyckStep.D) (2 * n - cut - iR) := by
    rwa [(rightHalf hc m).down_budget]
  have ha := pL.forcedOpening_mem_completion (leftHalf hc m) hiL hpreL hL
  have hb := pR.forcedOpening_mem_completion (rightHalf hc m) hiR hpreR hR
  have hoL := pL.forcedOpening_completion_ordinal (leftHalf hc m) hiL hpreL hL
  have hoR := pR.forcedOpening_completion_ordinal (rightHalf hc m) hiR hpreR hR
  apply inwardFIFO_sound m.val hc ha hb
  change ((oldOpenings (leftHalf hc m).word).filter (· < a.val)).card =
    ((oldOpenings (rightHalf hc m).word).filter (· < b.mirror.val)).card
  rw [hoL, hoR]
  exact hordinal

/-- Actual source prefixes satisfy exactly the original-counter emission criterion. -/
theorem BallotHalf.emitted_mem_iff {i h len H l : ℕ} (p : BallotHalf i h)
    (a : BallotHalf len H) (hi : i ≤ len) (hp : p.word = a.word.take i) :
    l ∈ forcedOpenings p (a.word.count DyckStep.D) (len - i) ↔
      l ∈ oldOpenings p.word ∧ ((oldOpenings p.word).filter (· < l)).card <
        i - a.word.count DyckStep.D - p.word.count DyckStep.D := by
  classical
  let suffix := p.completionSuffix a hi hp
  have hc : p.word.count DyckStep.D ≤ a.word.count DyckStep.D := by
    rw [hp]
    exact (List.take_sublist i a.word).count_le DyckStep.D
  have hd : a.word.count DyckStep.D - p.word.count DyckStep.D ≤ len - i := by
    have hh := (List.count_le_length (a := DyckStep.D) (l := suffix.word))
    rwa [suffix.count_down, suffix.length_word] at hh
  have hf : a.word.count DyckStep.D - p.word.count DyckStep.D ≤
      h + (len - i - (a.word.count DyckStep.D - p.word.count DyckStep.D)) := by
    have hh := suffix.prefix_nonneg suffix.word.length
    rw [List.take_length, Dyck.height_eq_count, suffix.count_down] at hh
    have counts := count_U_add_count_D suffix.word
    rw [suffix.count_down, suffix.length_word] at counts
    omega
  rw [forcedPrefix_exact p hc hd hf]
  exact Finset.mem_filter

/-- Joining a shared emitted ordinal is sound with the exact original down-counter tests. -/
theorem forcedFIFO_sound {n cut H iL hL iR hR : ℕ}
    (m : MatchingAtCut n cut H) (hc : cut ≤ 2 * n)
    (pL : BallotHalf iL hL) (pR : BallotHalf iR hR)
    (hiL : iL ≤ cut) (hiR : iR ≤ 2 * n - cut)
    (hpreL : pL.word = (leftHalf hc m).word.take iL)
    (hpreR : pR.word = (rightHalf hc m).word.take iR)
    {a b : Point n} (ha : a.val ∈ oldOpenings pL.word)
    (hb : b.mirror.val ∈ oldOpenings pR.word)
    (hordinal : ((oldOpenings pL.word).filter (· < a.val)).card =
      ((oldOpenings pR.word).filter (· < b.mirror.val)).card)
    (hEL : ((oldOpenings pL.word).filter (· < a.val)).card <
      iL - (cut - H) / 2 - pL.word.count DyckStep.D)
    (hER : ((oldOpenings pR.word).filter (· < b.mirror.val)).card <
      iR - (2 * n - cut - H) / 2 - pR.word.count DyckStep.D) : m.val.partner a = b := by
  apply forcedFIFO_source_sound m hc pL pR hiL hiR hpreL hpreR ?_ ?_ hordinal
  · have he := pL.emitted_mem_iff (l := a.val) (leftHalf hc m) hiL hpreL
    rw [(leftHalf hc m).down_budget] at he
    exact he.mpr ⟨ha, hEL⟩
  · have he := pR.emitted_mem_iff (l := b.mirror.val) (rightHalf hc m) hiR hpreR
    rw [(rightHalf hc m).down_budget] at he
    exact he.mpr ⟨hb, hER⟩

end Meanders.FirstCrossing
