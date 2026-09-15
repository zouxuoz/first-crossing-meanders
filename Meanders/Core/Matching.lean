import Meanders.Core.Arch
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Noncrossing perfect matchings

A *matching* on the rank-`n` boundary is a set of arches that pairwise share no
endpoint; it is *perfect* if every one of the `2n` boundary points is covered,
and *noncrossing* if no two of its arches interleave. `NoncrossingMatching n` bundles
the three conditions.

This is the literature definition, unchanged: nothing here is chosen for
computational convenience. What *is* arranged is that all three predicates are
decidable — they are bounded quantifiers over `Finset`s and over the `Fintype`
`Point n` — so `NoncrossingMatching n` has a genuine `DecidableEq` and later a genuine
`Fintype`, not a classical one.

The working tools built on top are `archAt` (the unique arch through a point,
extracted with `Finset.choose`, hence computable) and `partner`. The key
structural lemma is `properlyEncloses_of_mem`: an arch `a` of a noncrossing
matching *seals off* its own interior, so the partner of any point strictly
inside `a` is again strictly inside `a`. That is what makes the interval
`(a.left, a.right)` a smaller matching, and it is the engine of the Dyck-word
bijection in `Meanders.Core.Matching.Dyck`.
-/

namespace Meanders

variable {n : ℕ}

/-- Arches of `m` pairwise share no endpoint. -/
def IsMatching (m : Finset (Arch n)) : Prop :=
  ∀ a ∈ m, ∀ b ∈ m, a ≠ b → a.DisjointEndpoints b

/-- `m` is a matching and covers every boundary point. -/
def IsPerfect (m : Finset (Arch n)) : Prop :=
  IsMatching m ∧ ∀ v : Point n, ∃ a ∈ m, a.Contains v

/-- No two arches of `m` interleave. -/
def IsNoncrossing (m : Finset (Arch n)) : Prop :=
  ∀ a ∈ m, ∀ b ∈ m, ¬ a.Crosses b

instance (m : Finset (Arch n)) : Decidable (IsMatching m) := by
  unfold IsMatching; infer_instance

instance (m : Finset (Arch n)) : Decidable (IsPerfect m) := by
  unfold IsPerfect; infer_instance

instance (m : Finset (Arch n)) : Decidable (IsNoncrossing m) := by
  unfold IsNoncrossing; infer_instance

/-- A noncrossing perfect matching of the rank-`n` boundary: the object a
closed meander is a pair of. -/
@[ext]
structure NoncrossingMatching (n : ℕ) where
  /-- The arches. -/
  arches : Finset (Arch n)
  isPerfect : IsPerfect arches
  isNoncrossing : IsNoncrossing arches

namespace NoncrossingMatching

instance : DecidableEq (NoncrossingMatching n) := fun m m' =>
  decidable_of_iff (m.arches = m'.arches) ⟨NoncrossingMatching.ext, fun h => h ▸ rfl⟩

/-- The unique matching on no points. -/
def empty : NoncrossingMatching 0 :=
  ⟨∅, ⟨fun _a ha => absurd ha (Finset.notMem_empty _), fun v => v.elim0⟩,
    fun _a ha => absurd ha (Finset.notMem_empty _)⟩

@[simp] theorem empty_arches : empty.arches = ∅ := rfl

variable (m : NoncrossingMatching n)

theorem isMatching : IsMatching m.arches := m.isPerfect.1

theorem covers (v : Point n) : ∃ a ∈ m.arches, a.Contains v := m.isPerfect.2 v

theorem disjointEndpoints {a b : Arch n} (ha : a ∈ m.arches) (hb : b ∈ m.arches)
    (hne : a ≠ b) : a.DisjointEndpoints b := m.isMatching a ha b hb hne

theorem not_crosses {a b : Arch n} (ha : a ∈ m.arches) (hb : b ∈ m.arches) :
    ¬ a.Crosses b := m.isNoncrossing a ha b hb

/-- Two arches of `m` sharing an endpoint are equal. -/
theorem eq_of_contains {a b : Arch n} (ha : a ∈ m.arches) (hb : b ∈ m.arches) {v : Point n}
    (hav : a.Contains v) (hbv : b.Contains v) : a = b := by
  by_contra hne
  have hd := m.disjointEndpoints ha hb hne
  rw [Arch.disjoint_endpoints, Finset.disjoint_left] at hd
  exact hd (Arch.mem_endpoints.2 hav) (Arch.mem_endpoints.2 hbv)

/-- Every boundary point lies on exactly one arch. -/
theorem existsUnique_arch (v : Point n) : ∃! a, a ∈ m.arches ∧ a.Contains v := by
  obtain ⟨a, ha, hav⟩ := m.covers v
  exact ⟨a, ⟨ha, hav⟩, fun _ ⟨hb, hbv⟩ => m.eq_of_contains hb ha hbv hav⟩

/-- The unique arch of `m` through `v`. Computable: `Finset.choose` picks the
witness out of the `Finset` itself. -/
def archAt (v : Point n) : Arch n :=
  m.arches.choose (fun a : Arch n => a.Contains v) (m.existsUnique_arch v)

@[simp] theorem archAt_mem (v : Point n) : m.archAt v ∈ m.arches :=
  m.arches.choose_mem (fun a : Arch n => a.Contains v) (m.existsUnique_arch v)

@[simp] theorem archAt_contains (v : Point n) : (m.archAt v).Contains v :=
  m.arches.choose_property (fun a : Arch n => a.Contains v) (m.existsUnique_arch v)

theorem archAt_eq {a : Arch n} (ha : a ∈ m.arches) {v : Point n} (hav : a.Contains v) :
    m.archAt v = a :=
  m.eq_of_contains (m.archAt_mem v) ha (m.archAt_contains v) hav

@[simp] theorem archAt_left {a : Arch n} (ha : a ∈ m.arches) : m.archAt a.left = a :=
  m.archAt_eq ha a.contains_left

@[simp] theorem archAt_right {a : Arch n} (ha : a ∈ m.arches) : m.archAt a.right = a :=
  m.archAt_eq ha a.contains_right

/-- The point matched to `v`. -/
def partner (v : Point n) : Point n :=
  if v = (m.archAt v).left then (m.archAt v).right else (m.archAt v).left

@[simp] theorem partner_left {a : Arch n} (ha : a ∈ m.arches) : m.partner a.left = a.right := by
  simp [partner, m.archAt_left ha]

@[simp] theorem partner_right {a : Arch n} (ha : a ∈ m.arches) : m.partner a.right = a.left := by
  simp [partner, m.archAt_right ha, a.left_ne_right.symm]

/-- Reading the partner map off the arch it comes from: the standard way to
case on `partner`. -/
theorem exists_arch_partner (v : Point n) :
    ∃ a ∈ m.arches, (a.left = v ∧ a.right = m.partner v) ∨
      (a.right = v ∧ a.left = m.partner v) := by
  obtain ⟨a, ha, hav⟩ := m.covers v
  refine ⟨a, ha, ?_⟩
  rcases hav with rfl | rfl
  · exact Or.inl ⟨rfl, (m.partner_left ha).symm⟩
  · exact Or.inr ⟨rfl, (m.partner_right ha).symm⟩

theorem partner_ne (v : Point n) : m.partner v ≠ v := by
  obtain ⟨a, ha, ⟨rfl, hp⟩ | ⟨rfl, hp⟩⟩ := m.exists_arch_partner v
  · rw [← hp]; exact a.left_ne_right.symm
  · rw [← hp]; exact a.left_ne_right

@[simp] theorem partner_partner (v : Point n) : m.partner (m.partner v) = v := by
  obtain ⟨a, ha, ⟨rfl, hp⟩ | ⟨rfl, hp⟩⟩ := m.exists_arch_partner v
  · rw [← hp]; exact m.partner_right ha
  · rw [← hp]; exact m.partner_left ha

/-- **The sealing lemma.** In a noncrossing matching, an arch `a` properly
encloses every arch that touches the open interval `(a.left, a.right)`.
Equivalently: arches never leak out of the interval they start in. -/
theorem properlyEncloses_of_mem {a b : Arch n} (ha : a ∈ m.arches) (hb : b ∈ m.arches)
    {v : Point n} (hbv : b.Contains v) (h₁ : a.left < v) (h₂ : v < a.right) :
    a.ProperlyEncloses b := by
  have hbl : b.left ≤ v := Arch.left_le_of_contains hbv
  have hbr : v ≤ b.right := Arch.le_right_of_contains hbv
  have hne : a ≠ b := by
    rintro rfl
    rcases hbv with rfl | rfl
    exacts [absurd h₁ (lt_irrefl _), absurd h₂ (lt_irrefl _)]
  rcases Arch.separated_or_nested (m.disjointEndpoints ha hb hne) (m.not_crosses ha hb) with
    h | h | h | h
  · exact absurd (h.trans_le hbl) (not_lt.2 h₂.le)
  · exact absurd (h.trans_le h₁.le) (not_lt.2 hbr)
  · exact h
  · exact absurd hbv (by
      rcases hbv with rfl | rfl
      exacts [absurd h.1 (not_lt.2 h₁.le), absurd h.2 (not_lt.2 h₂.le)])

/-- The partner of a point strictly inside `a` is strictly inside `a`: the
interior of an arch is matched among itself. -/
theorem partner_mem_interior {a : Arch n} (ha : a ∈ m.arches) {v : Point n}
    (h₁ : a.left < v) (h₂ : v < a.right) :
    a.left < m.partner v ∧ m.partner v < a.right := by
  obtain ⟨b, hb, ⟨rfl, hp⟩ | ⟨rfl, hp⟩⟩ := m.exists_arch_partner v
  · obtain ⟨hl, hr⟩ := m.properlyEncloses_of_mem ha hb b.contains_left h₁ h₂
    rw [← hp]; exact ⟨hl.trans b.ordered, hr⟩
  · obtain ⟨hl, hr⟩ := m.properlyEncloses_of_mem ha hb b.contains_right h₁ h₂
    rw [← hp]; exact ⟨hl, b.ordered.trans hr⟩

/-- Membership in `m.arches` is exactly "these two points are partners". -/
theorem mem_arches_iff (a : Arch n) : a ∈ m.arches ↔ m.partner a.left = a.right := by
  refine ⟨fun ha => m.partner_left ha, fun h => ?_⟩
  obtain ⟨b, hb, ⟨hbl, hbp⟩ | ⟨hbr, hbp⟩⟩ := m.exists_arch_partner a.left
  · exact (Arch.ext hbl (hbp.trans h) : b = a) ▸ hb
  · exact absurd a.ordered (by rw [← hbr, ← (hbp.trans h)]; exact not_lt.2 b.ordered.le)

/-- The arch `{x, y}` with `x < y` belongs to `m` exactly when `x` and `y` are partners. -/
theorem mk_mem_arches {x y : Point n} (hlt : x < y) (hxy : m.partner x = y) :
    (⟨x, y, hlt⟩ : Arch n) ∈ m.arches := by
  obtain ⟨a, ha, ⟨hal, har⟩ | ⟨har, hal⟩⟩ := m.exists_arch_partner x
  · exact (Arch.ext hal (har.trans hxy) : a = ⟨x, y, hlt⟩) ▸ ha
  · exact absurd (hxy ▸ hal ▸ har ▸ a.ordered : y < x) (not_lt.2 hlt.le)

/-- **No interleaving.** Four points `x < u < y < v` are never matched as
`x ↔ y` and `u ↔ v`: that is a crossing. -/
theorem not_interleave {x y u v : Point n} (hxy : m.partner x = y) (huv : m.partner u = v)
    (h₁ : x < u) (h₂ : u < y) (h₃ : y < v) : False :=
  m.not_crosses (m.mk_mem_arches (h₁.trans h₂) hxy) (m.mk_mem_arches (h₂.trans h₃) huv)
    (Or.inl ⟨h₁, h₂, h₃⟩)

/-! ## Building a matching from its partner function -/

/-- The three conditions under which `f` is the partner function of a
noncrossing perfect matching: an involution, without fixed points, and with
no interleaved pairs `x < u < f x < f u`. -/
structure IsPartnerFn (f : Point n → Point n) : Prop where
  involutive : ∀ v, f (f v) = v
  ne : ∀ v, f v ≠ v
  noncrossing : ∀ x u, x < u → u < f x → f x < f u → False

/-- The matching whose arches are the pairs `{v, f v}`. -/
def ofPartner (f : Point n → Point n) (hf : IsPartnerFn f) : NoncrossingMatching n where
  arches := Finset.univ.filter fun a : Arch n => f a.left = a.right
  isPerfect := by
    refine ⟨fun a ha b hb hne => ?_, fun v => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      refine ⟨fun h => hne (Arch.ext h (by rw [← ha, ← hb, h])), fun h => ?_, fun h => ?_,
        fun h => hne (Arch.ext ?_ h)⟩
      · have h1 : a.right = b.left := by rw [← ha, h, ← hb, hf.involutive]
        exact absurd ((a.ordered.trans_eq h1).trans (b.ordered.trans_eq h.symm)) (lt_irrefl _)
      · have h1 : b.right = a.left := by rw [← hb, ← h, ← ha, hf.involutive]
        exact absurd ((b.ordered.trans_eq h1).trans (a.ordered.trans_eq h)) (lt_irrefl _)
      · have := hf.involutive a.left
        rw [ha, h, ← hb, hf.involutive] at this
        exact this.symm
    · rcases lt_or_gt_of_ne (hf.ne v) with hlt | hlt
      · exact ⟨⟨f v, v, hlt⟩, by simp [hf.involutive], Or.inr rfl⟩
      · exact ⟨⟨v, f v, hlt⟩, by simp, Or.inl rfl⟩
  isNoncrossing := by
    intro a ha b hb hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases hc with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
    · exact hf.noncrossing a.left b.left h₁ (ha ▸ h₂) (ha ▸ hb ▸ h₃)
    · exact hf.noncrossing b.left a.left h₁ (hb ▸ h₂) (hb ▸ ha ▸ h₃)

@[simp] theorem partner_ofPartner (f : Point n → Point n) (hf : IsPartnerFn f) (v : Point n) :
    (ofPartner f hf).partner v = f v := by
  rcases lt_or_gt_of_ne (hf.ne v) with hlt | hlt
  · have hmem : (⟨f v, v, hlt⟩ : Arch n) ∈ (ofPartner f hf).arches := by
      simp [ofPartner, hf.involutive]
    exact (ofPartner f hf).partner_right hmem
  · have hmem : (⟨v, f v, hlt⟩ : Arch n) ∈ (ofPartner f hf).arches := by simp [ofPartner]
    exact (ofPartner f hf).partner_left hmem

/-- Two matchings with the same partner function are equal. -/
theorem ext_partner {m m' : NoncrossingMatching n} (h : ∀ v, m.partner v = m'.partner v) : m = m' :=
    by
  apply NoncrossingMatching.ext
  ext a
  rw [m.mem_arches_iff a, m'.mem_arches_iff a, h]

end NoncrossingMatching

end Meanders
