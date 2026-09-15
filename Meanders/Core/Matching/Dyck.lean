import Meanders.Core.Matching
import Meanders.Core.Word
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Noncrossing matchings are balanced words

This file proves the classical bijection

  `NoncrossingMatching n ≃ {w : DyckWord // w.semilength = n}`

and, as a corollary, `Fintype.card (NoncrossingMatching n) = catalan n`.

The two directions are:

* `NoncrossingMatching.wordOf`: write `U` at every left endpoint and `D` at every right
  endpoint. `NoncrossingMatching.paired_wordOf` says the arches of `m` are exactly the
  pairs the height rule of `Meanders.Paired` picks out of `m.wordOf`. Its proof
  is a sign-counting argument: the interior of an arch is closed under
  `partner` (`NoncrossingMatching.partner_mem_interior`), so the `+1`s and `-1`s inside
  an arch cancel exactly, and cancel at worst partially on any shorter prefix.
* `ofDyck`: read the pairs of a balanced word off the height rule. Here the
  work is done by `exists_paired_of_U` / `exists_paired_of_D` in
  `Meanders.Core.Word`.

Both directions are computable. The bijection transports Mathlib's
Catalan-sized `Fintype` of Dyck words to `NoncrossingMatching`, so enumeration does not
scan all raw words of length `2n`.
-/

namespace Meanders

open DyckStep Finset

variable {n : ℕ} {w : List DyckStep} {i j k l : ℕ}

namespace NoncrossingMatching

variable (m : NoncrossingMatching n)

/-! ## The partner map on `ℕ` -/

/-- `partner` transported to `ℕ`, fixing everything off the boundary. Working
with `ℕ` indices is what lets the arch side talk to the word side. -/
def partnerIndex (i : ℕ) : ℕ := if h : i < 2 * n then (m.partner ⟨i, h⟩ : ℕ) else i

@[simp] theorem partnerIndex_coe (v : Point n) : m.partnerIndex (v : ℕ) = (m.partner v : ℕ) := by
  rw [partnerIndex, dite_eq_left v.isLt]

theorem partnerIndex_eq (hi : i < 2 * n) : m.partnerIndex i = ((m.partner ⟨i, hi⟩ : Point n) : ℕ) :=
    by
  rw [partnerIndex, dite_eq_left hi]

theorem partnerIndex_lt (hi : i < 2 * n) : m.partnerIndex i < 2 * n := by
  rw [m.partnerIndex_eq hi]; exact (m.partner ⟨i, hi⟩).isLt

theorem partnerIndex_ne (hi : i < 2 * n) : m.partnerIndex i ≠ i := by
  rw [m.partnerIndex_eq hi]
  intro h
  exact m.partner_ne ⟨i, hi⟩ (Fin.ext h)

theorem partnerIndex_partnerIndex (hi : i < 2 * n) : m.partnerIndex (m.partnerIndex i) = i := by
  rw [m.partnerIndex_eq hi, partnerIndex_coe, partner_partner]

theorem partnerIndex_left {a : Arch n} (ha : a ∈ m.arches) : m.partnerIndex (a.left : ℕ) =
    (a.right : ℕ) := by
  rw [partnerIndex_coe, m.partner_left ha]

theorem partnerIndex_right {a : Arch n} (ha : a ∈ m.arches) : m.partnerIndex (a.right : ℕ) =
    (a.left : ℕ) := by
  rw [partnerIndex_coe, m.partner_right ha]

/-- The sealing lemma, on `ℕ` indices: the interior of an arch is closed under
`partnerIndex`. -/
theorem partnerIndex_mem_interior {a : Arch n} (ha : a ∈ m.arches)
    (h₁ : (a.left : ℕ) < i) (h₂ : i < (a.right : ℕ)) :
    (a.left : ℕ) < m.partnerIndex i ∧ m.partnerIndex i < (a.right : ℕ) := by
  have hi : i < 2 * n := lt_trans h₂ a.right.isLt
  have := m.partner_mem_interior ha (v := ⟨i, hi⟩) h₁ h₂
  rw [partnerIndex, dite_eq_left hi]
  exact this

/-! ## Signs and cancellation -/

/-- `+1` at a left endpoint, `-1` at a right endpoint. -/
def endpointSign (i : ℕ) : ℤ := if i < m.partnerIndex i then 1 else -1

theorem sum_endpointSign (T : Finset ℕ) :
    ∑ p ∈ T, m.endpointSign p =
      ((T.filter fun p => p < m.partnerIndex p).card : ℤ) -
        ((T.filter fun p => ¬ p < m.partnerIndex p).card : ℤ) := by
  simp only [endpointSign]
  rw [Finset.sum_ite]
  simp [sub_eq_add_neg]

/-- Right endpoints inject into left endpoints, via `partnerIndex`. -/
theorem card_closers_le (T : Finset ℕ) (hsub : ∀ p ∈ T, p < 2 * n)
    (hcl : ∀ p ∈ T, m.partnerIndex p < p → m.partnerIndex p ∈ T) :
    (T.filter fun p => ¬ p < m.partnerIndex p).card ≤
      (T.filter fun p => p < m.partnerIndex p).card := by
  refine Finset.card_le_card_of_injOn m.partnerIndex (fun p hp => ?_) (fun p hp q hq h => ?_)
  · simp only [Finset.mem_coe, Finset.mem_filter, not_lt] at hp ⊢
    obtain ⟨hpT, hp'⟩ := hp
    have hlt : m.partnerIndex p < p := lt_of_le_of_ne hp' (m.partnerIndex_ne (hsub p hpT))
    exact ⟨hcl p hpT hlt, by rw [m.partnerIndex_partnerIndex (hsub p hpT)]; exact hlt⟩
  · simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
    rw [← m.partnerIndex_partnerIndex (hsub p hp.1), ← m.partnerIndex_partnerIndex (hsub q hq.1), h]

/-- Left endpoints inject into right endpoints when `T` is closed under `partnerIndex`. -/
theorem card_openers_le (T : Finset ℕ) (hsub : ∀ p ∈ T, p < 2 * n)
    (hcl : ∀ p ∈ T, m.partnerIndex p ∈ T) :
    (T.filter fun p => p < m.partnerIndex p).card ≤
      (T.filter fun p => ¬ p < m.partnerIndex p).card := by
  refine Finset.card_le_card_of_injOn m.partnerIndex (fun p hp => ?_) (fun p hp q hq h => ?_)
  · simp only [Finset.mem_coe, Finset.mem_filter, not_lt] at hp ⊢
    obtain ⟨hpT, hp'⟩ := hp
    exact ⟨hcl p hpT, by rw [m.partnerIndex_partnerIndex (hsub p hpT)]; omega⟩
  · simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
    rw [← m.partnerIndex_partnerIndex (hsub p hp.1), ← m.partnerIndex_partnerIndex (hsub q hq.1), h]

/-- On a set closed under `partnerIndex` the signs cancel exactly. -/
theorem sum_endpointSign_eq_zero (T : Finset ℕ) (hsub : ∀ p ∈ T, p < 2 * n)
    (hcl : ∀ p ∈ T, m.partnerIndex p ∈ T) : ∑ p ∈ T, m.endpointSign p = 0 := by
  have h₁ := m.card_closers_le T hsub fun p hp _ => hcl p hp
  have h₂ := m.card_openers_le T hsub hcl
  rw [m.sum_endpointSign T]
  omega

/-- On a set that contains the partner of each of its right endpoints, the
signs cancel at worst partially. -/
theorem sum_endpointSign_nonneg (T : Finset ℕ) (hsub : ∀ p ∈ T, p < 2 * n)
    (hcl : ∀ p ∈ T, m.partnerIndex p < p → m.partnerIndex p ∈ T) : 0 ≤ ∑ p ∈ T, m.endpointSign p :=
      by
  have := m.card_closers_le T hsub hcl
  rw [m.sum_endpointSign T]
  omega

/-! ## The word of a matching -/

/-- `U` at each left endpoint, `D` at each right endpoint. -/
def wordOf : List DyckStep :=
  (List.range (2 * n)).map fun i => if i < m.partnerIndex i then U else D

@[simp] theorem length_wordOf : m.wordOf.length = 2 * n := by simp [wordOf]

theorem getElem?_wordOf (hk : k < 2 * n) :
    m.wordOf[k]? = some (if k < m.partnerIndex k then U else D) := by
  simp [wordOf, hk]

theorem step_wordOf (hk : k < 2 * n) :
    ((m.wordOf[k]?).map stepHeight).getD 0 = m.endpointSign k := by
  rw [m.getElem?_wordOf hk]
  by_cases h : k < m.partnerIndex k <;> simp [h, endpointSign, stepHeight]

theorem height_wordOf (hi : i ≤ 2 * n) :
    height m.wordOf i = ∑ p ∈ Finset.range i, m.endpointSign p := by
  induction i with
  | zero => simp
  | succ k ih =>
    rw [height_succ, ih (by omega), Finset.sum_range_succ, m.step_wordOf (by omega)]

theorem height_wordOf_sub (hl : l ≤ i) (hi : i ≤ 2 * n) :
    height m.wordOf i - height m.wordOf l = ∑ p ∈ Finset.Ico l i, m.endpointSign p := by
  rw [m.height_wordOf hi, m.height_wordOf (le_trans hl hi), Finset.sum_Ico_eq_sub _ hl]

theorem endpointSign_left {a : Arch n} (ha : a ∈ m.arches) : m.endpointSign (a.left : ℕ) = 1 := by
  simp [endpointSign, m.partnerIndex_left ha, a.ordered]

theorem endpointSign_right {a : Arch n} (ha : a ∈ m.arches) : m.endpointSign (a.right : ℕ) = -1 :=
    by
  simp [endpointSign, m.partnerIndex_right ha, not_lt.2 a.ordered.le]

/-- **Every arch is a matched pair of the word.** -/
theorem paired_wordOf {a : Arch n} (ha : a ∈ m.arches) :
    Paired m.wordOf (a.left : ℕ) (a.right : ℕ) := by
  have hord : (a.left : ℕ) < (a.right : ℕ) := a.ordered
  have hr : (a.right : ℕ) < 2 * n := a.right.isLt
  refine ⟨by rw [m.length_wordOf]; exact hr, hord, ?_, ?_⟩
  · -- the signs strictly inside `a` cancel, and the two endpoints cancel each other
    have hzero : ∑ p ∈ Finset.Ico ((a.left : ℕ) + 1) (a.right : ℕ), m.endpointSign p = 0 := by
      refine m.sum_endpointSign_eq_zero _ (fun p hp => ?_) (fun p hp => ?_)
      · rw [Finset.mem_Ico] at hp; omega
      · rw [Finset.mem_Ico] at hp ⊢
        have := m.partnerIndex_mem_interior ha (i := p) (by omega) (by omega)
        omega
    have hsplit : ∑ p ∈ Finset.Ico (a.left : ℕ) ((a.right : ℕ) + 1), m.endpointSign p = 0 := by
      rw [Finset.sum_Ico_succ_top (by omega), Finset.sum_eq_sum_Ico_succ_bot (by omega),
        hzero, m.endpointSign_left ha, m.endpointSign_right ha]
      ring
    have := m.height_wordOf_sub (l := (a.left : ℕ)) (i := (a.right : ℕ) + 1)
      (by omega) (by omega)
    rw [hsplit] at this
    omega
  · intro j hj hjl
    have hnn : 0 ≤ ∑ p ∈ Finset.Ico ((a.left : ℕ) + 1) (j + 1), m.endpointSign p := by
      refine m.sum_endpointSign_nonneg _ (fun p hp => ?_) (fun p hp hlt => ?_)
      · rw [Finset.mem_Ico] at hp; omega
      · rw [Finset.mem_Ico] at hp ⊢
        have := m.partnerIndex_mem_interior ha (i := p) (by omega) (by omega)
        omega
    have hsplit : ∑ p ∈ Finset.Ico (a.left : ℕ) (j + 1), m.endpointSign p =
        1 + ∑ p ∈ Finset.Ico ((a.left : ℕ) + 1) (j + 1), m.endpointSign p := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), m.endpointSign_left ha]
    have := m.height_wordOf_sub (l := (a.left : ℕ)) (i := j + 1) (by omega) (by omega)
    rw [hsplit] at this
    omega

theorem isDyck_wordOf : IsDyck n m.wordOf := by
  refine ⟨m.length_wordOf, ?_, fun i hi => ?_⟩
  · rw [m.height_wordOf le_rfl]
    refine m.sum_endpointSign_eq_zero _ (fun p hp => Finset.mem_range.1 hp) (fun p hp => ?_)
    exact Finset.mem_range.2 (m.partnerIndex_lt (Finset.mem_range.1 hp))
  · rw [m.height_wordOf hi]
    refine m.sum_endpointSign_nonneg _ (fun p hp => lt_of_lt_of_le (Finset.mem_range.1 hp) hi)
      (fun p hp hlt => Finset.mem_range.2 (lt_trans hlt (Finset.mem_range.1 hp)))

end NoncrossingMatching

/-! ## The matching of a word -/

/-- The arches a word prescribes, via the height rule. Decidable, hence
computable. -/
def archesOfWord (n : ℕ) (w : List DyckStep) : Finset (Arch n) :=
  Finset.univ.filter fun a => Paired w (a.left : ℕ) (a.right : ℕ)

@[simp] theorem mem_archesOfWord {a : Arch n} :
    a ∈ archesOfWord n w ↔ Paired w (a.left : ℕ) (a.right : ℕ) := by
  simp [archesOfWord]

theorem NoncrossingMatching.archesOfWord_wordOf (m : NoncrossingMatching n) :
    archesOfWord n m.wordOf = m.arches := by
  ext a
  refine ⟨fun ha => ?_, fun ha => mem_archesOfWord.2 (m.paired_wordOf ha)⟩
  rw [mem_archesOfWord] at ha
  -- `a.left` opens in `m.wordOf`, so it is the left endpoint of its own arch in `m`
  have hU := ha.isU
  rw [m.getElem?_wordOf a.left.isLt] at hU
  have hlt : (a.left : ℕ) < m.partnerIndex (a.left : ℕ) := by
    by_contra hc
    rw [ite_eq_right hc] at hU
    exact absurd hU (by simp)
  obtain ⟨b, hb, ⟨hbl, hbp⟩ | ⟨hbr, hbp⟩⟩ := m.exists_arch_partner a.left
  · have hright : (a.right : ℕ) = (b.right : ℕ) :=
      ha.right_unique (hbl ▸ m.paired_wordOf hb)
    exact (Arch.ext hbl.symm (Fin.ext hright) : a = b) ▸ hb
  · exact absurd hlt (by rw [partnerIndex_coe, ← hbp, ← hbr]; exact not_lt.2 b.ordered.le)

/-- Matched pairs never cross, so the arches a word prescribes are automatically
noncrossing — no balancedness needed. -/
theorem isNoncrossing_archesOfWord (n : ℕ) (w : List DyckStep) :
    IsNoncrossing (archesOfWord n w) := by
  intro a ha b hb hcross
  have hpa := mem_archesOfWord.1 ha
  have hpb := mem_archesOfWord.1 hb
  rcases hcross with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact absurd (hpa.nested_of_lt hpb h1 h2) (not_lt.2 (le_of_lt h3))
  · exact absurd (hpb.nested_of_lt hpa h1 h2) (not_lt.2 (le_of_lt h3))

section OfDyck

variable {n : ℕ} {w : List DyckStep} (h : IsDyck n w)
include h

theorem isPerfect_archesOfWord : IsPerfect (archesOfWord n w) := by
  constructor
  · intro a ha b hb hne
    have hpa := mem_archesOfWord.1 ha
    have hpb := mem_archesOfWord.1 hb
    refine ⟨fun hc => hne ?_, fun hc => ?_, fun hc => ?_, fun hc => hne ?_⟩
    · have hv : (a.left : ℕ) = (b.left : ℕ) := congrArg Fin.val hc
      rw [← hv] at hpb
      exact Arch.ext hc (Fin.ext (hpa.right_unique hpb))
    · have hv : (a.left : ℕ) = (b.right : ℕ) := congrArg Fin.val hc
      have h1 := hpa.isU
      rw [hv, hpb.isD] at h1
      exact absurd h1 (by simp)
    · have hv : (a.right : ℕ) = (b.left : ℕ) := congrArg Fin.val hc
      have h1 := hpa.isD
      rw [hv, hpb.isU] at h1
      exact absurd h1 (by simp)
    · have hv : (a.right : ℕ) = (b.right : ℕ) := congrArg Fin.val hc
      rw [← hv] at hpb
      exact Arch.ext (Fin.ext (hpa.left_unique hpb)) hc
  · intro v
    have hv : (v : ℕ) < w.length := by rw [h.length]; exact v.isLt
    rcases getElem?_eq_U_or_D hv with hU | hD
    · obtain ⟨r, hr⟩ := exists_paired_of_U hv hU (by
        rw [h.height_length]; exact h.height_nonneg _)
      have hrlt : r < 2 * n := by rw [← h.length]; exact hr.lt_length
      refine ⟨⟨v, ⟨r, hrlt⟩, hr.lt⟩, mem_archesOfWord.2 hr, Or.inl rfl⟩
    · obtain ⟨l, hl⟩ := exists_paired_of_D hv hD (h.height_nonneg _)
      have hllt : l < 2 * n := by
        have := hl.left_lt_length; rw [h.length] at this; exact this
      exact ⟨⟨⟨l, hllt⟩, v, hl.lt⟩, mem_archesOfWord.2 hl, Or.inr rfl⟩

/-- The noncrossing perfect matching a balanced word describes. -/
def ofDyck : NoncrossingMatching n :=
  ⟨archesOfWord n w, isPerfect_archesOfWord h, isNoncrossing_archesOfWord n w⟩

@[simp] theorem ofDyck_arches : (ofDyck h).arches = archesOfWord n w := rfl

theorem wordOf_ofDyck : (ofDyck h).wordOf = w := by
  refine List.ext_getElem (by rw [NoncrossingMatching.length_wordOf, h.length]) fun i h₁ h₂ => ?_
  rw [NoncrossingMatching.length_wordOf] at h₁
  have hkey : (i < (ofDyck h).partnerIndex i) ↔ w[i]? = some U := by
    constructor
    · intro hlt
      obtain ⟨b, hb, ⟨hbl, hbp⟩ | ⟨hbr, hbp⟩⟩ :=
        (ofDyck h).exists_arch_partner ⟨i, h₁⟩
      · have := mem_archesOfWord.1 (by rwa [← ofDyck_arches h])
        rw [show (b.left : ℕ) = i from congrArg Fin.val hbl] at this
        exact this.isU
      · exfalso
        have hib : i = (b.right : ℕ) := (congrArg Fin.val hbr).symm
        rw [hib, NoncrossingMatching.partnerIndex_coe, (ofDyck h).partner_right hb] at hlt
        have hord : (b.left : ℕ) < (b.right : ℕ) := b.ordered
        omega
    · intro hU
      obtain ⟨r, hr⟩ := exists_paired_of_U (by rw [h.length]; exact h₁) hU (by
        rw [h.height_length]; exact h.height_nonneg _)
      have hrlt : r < 2 * n := by rw [← h.length]; exact hr.lt_length
      have hmem : (⟨⟨i, h₁⟩, ⟨r, hrlt⟩, hr.lt⟩ : Arch n) ∈ (ofDyck h).arches :=
        mem_archesOfWord.2 hr
      rw [show i = ((⟨⟨i, h₁⟩, ⟨r, hrlt⟩, hr.lt⟩ : Arch n).left : ℕ) from rfl,
        (ofDyck h).partnerIndex_left hmem]
      exact hr.lt
  have hget : (ofDyck h).wordOf[i] = if i < (ofDyck h).partnerIndex i then U else D := by
    have := (ofDyck h).getElem?_wordOf h₁
    rw [List.getElem?_eq_getElem (by rw [NoncrossingMatching.length_wordOf]; exact h₁)] at this
    exact Option.some_injective _ this
  rw [hget]
  rcases getElem?_eq_U_or_D h₂ with hU | hD
  · rw [ite_eq_left (hkey.2 hU)]
    exact (Option.some_injective _ ((List.getElem?_eq_getElem h₂).symm.trans hU)).symm
  · rw [ite_eq_right (fun hc => by rw [hkey.1 hc] at hD; exact absurd hD (by simp))]
    exact (Option.some_injective _ ((List.getElem?_eq_getElem h₂).symm.trans hD)).symm

end OfDyck

/-- **The Dyck-word bijection.** -/
def equivDyckWord (n : ℕ) : NoncrossingMatching n ≃ {p : DyckWord // p.semilength = n} where
  toFun m := ⟨m.isDyck_wordOf.toDyckWord, m.isDyck_wordOf.semilength_toDyckWord⟩
  invFun p := ofDyck (isDyck_of_dyckWord p.1 p.2)
  left_inv m := NoncrossingMatching.ext (by rw [ofDyck_arches]; exact m.archesOfWord_wordOf)
  right_inv p := Subtype.ext (DyckWord.ext (wordOf_ofDyck _))

/-! ## Enumeration, `Fintype`, and the Catalan count -/

/-- Mathlib enumerates Dyck words of semilength `n` through binary trees with
`n` nodes. Transport that finite structure across the Dyck-word bijection. -/
instance : Fintype (NoncrossingMatching n) :=
  Fintype.ofEquiv _ (equivDyckWord n).symm

/-- Every noncrossing perfect matching of rank `n`, represented directly as a
finite set. -/
def enumerateNoncrossingMatchings (n : ℕ) : Finset (NoncrossingMatching n) := Finset.univ

@[simp] theorem mem_enumerateNoncrossingMatchings (m : NoncrossingMatching n) :
    m ∈ enumerateNoncrossingMatchings n := Finset.mem_univ m

/-- **Noncrossing perfect matchings are counted by the Catalan numbers.** -/
theorem card_noncrossingMatching_eq_catalan (n : ℕ) :
    Fintype.card (NoncrossingMatching n) = catalan n := by
  rw [Fintype.card_congr (equivDyckWord n), DyckWord.card_dyckWord_semilength_eq_catalan]

end Meanders
