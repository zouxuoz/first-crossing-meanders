import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Interval.Finset.Fin

/-!
# Arches on a numbered boundary

The boundary of a rank-`n` diagram is the ordered set of points
`0 < 1 < ⋯ < 2n-1`, i.e. `Fin (2 * n)`. An *arch* joins two distinct points;
we represent it canonically by its smaller and larger endpoint, so that the
unordered pair `{i, j}` has exactly one representation.

Everything here is decidable by construction: `Arch n` gets its `DecidableEq`
and `Fintype` instances from the ordered-pair subtype of `Fin (2n) × Fin (2n)`,
and each relation between arches is a Boolean combination of `Fin`
comparisons. Nothing in this file is classical, which is what later lets
`Meanders.countClosedMeanders` actually run.

The one substantive lemma is `Arch.separated_or_nested`: two endpoint-disjoint
arches that do not cross are either side by side or one inside the other. That
trichotomy is the whole geometric content of "noncrossing", and every later
argument about noncrossing matchings goes through it.
-/

namespace Meanders

variable {n : ℕ}

/-- The `2 * n` boundary points of a rank-`n` diagram, ordered `0 < ⋯ < 2n-1`. -/
abbrev Point (n : ℕ) := Fin (2 * n)

/-- The point mirrored across the middle of the boundary: `v ↦ 2n - 1 - v`.
This is the standard order-reversing involution `Fin.rev`. -/
abbrev Point.mirror (v : Point n) : Point n := Fin.rev v

theorem Point.mirror_val (v : Point n) : (v.mirror : ℕ) = 2 * n - 1 - v := by
  change 2 * n - ((v : ℕ) + 1) = 2 * n - 1 - v
  omega

theorem Point.mirror_mirror (v : Point n) : v.mirror.mirror = v := Fin.rev_rev v

theorem Point.mirror_injective : Function.Injective (@Point.mirror n) :=
  Fin.rev_involutive.injective

theorem Point.mirror_lt_mirror {u v : Point n} : u.mirror < v.mirror ↔ v < u :=
  Fin.rev_lt_rev

/-- An arch on the rank-`n` boundary: two distinct boundary points, given in
increasing order. -/
@[ext]
structure Arch (n : ℕ) where
  /-- The smaller endpoint. -/
  left : Point n
  /-- The larger endpoint. -/
  right : Point n
  ordered : left < right

namespace Arch

variable {n : ℕ} {a b : Arch n}

/-- `Arch n` is literally the subtype of increasing pairs. This equivalence is
where its computable `Fintype` instance comes from. -/
def equivOrderedPair : Arch n ≃ {p : Point n × Point n // p.1 < p.2} where
  toFun a := ⟨(a.left, a.right), a.ordered⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : DecidableEq (Arch n) := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    ⟨fun h => Arch.ext h.1 h.2, fun h => h ▸ ⟨rfl, rfl⟩⟩

instance : Fintype (Arch n) := Fintype.ofEquiv _ equivOrderedPair.symm

theorem left_ne_right (a : Arch n) : a.left ≠ a.right := ne_of_lt a.ordered

/-- `v` is an endpoint of `a`. -/
def Contains (a : Arch n) (v : Point n) : Prop := v = a.left ∨ v = a.right

instance (a : Arch n) (v : Point n) : Decidable (a.Contains v) := by
  unfold Contains; infer_instance

@[simp] theorem contains_left (a : Arch n) : a.Contains a.left := Or.inl rfl
@[simp] theorem contains_right (a : Arch n) : a.Contains a.right := Or.inr rfl

theorem left_le_of_contains {a : Arch n} {v : Point n} (h : a.Contains v) : a.left ≤ v := by
  have := a.ordered
  grind [Contains]

theorem le_right_of_contains {a : Arch n} {v : Point n} (h : a.Contains v) : v ≤ a.right := by
  have := a.ordered
  grind [Contains]

/-- The two endpoints of `a`, as a `Finset`. -/
def endpoints (a : Arch n) : Finset (Point n) := {a.left, a.right}

@[simp] theorem mem_endpoints {a : Arch n} {v : Point n} :
    v ∈ a.endpoints ↔ a.Contains v := by simp [endpoints, Contains]

@[simp] theorem card_endpoints (a : Arch n) : a.endpoints.card = 2 := by
  simp [endpoints, a.left_ne_right]

/-- `a` and `b` share no endpoint. Stated as four `≠`s rather than
`Disjoint a.endpoints b.endpoints` so that deciding it is four comparisons;
`disjoint_endpoints` says the two formulations agree. -/
def DisjointEndpoints (a b : Arch n) : Prop :=
  a.left ≠ b.left ∧ a.left ≠ b.right ∧ a.right ≠ b.left ∧ a.right ≠ b.right

instance (a b : Arch n) : Decidable (a.DisjointEndpoints b) := by
  unfold DisjointEndpoints; infer_instance

theorem disjoint_endpoints (a b : Arch n) :
    a.DisjointEndpoints b ↔ Disjoint a.endpoints b.endpoints := by
  simp only [DisjointEndpoints, Finset.disjoint_left, endpoints]
  aesop

theorem DisjointEndpoints.symm (h : a.DisjointEndpoints b) : b.DisjointEndpoints a :=
  by grind [DisjointEndpoints]

theorem DisjointEndpoints.ne (h : a.DisjointEndpoints b) : a ≠ b := by
  grind [DisjointEndpoints]

/-- `b` lies strictly inside `a`. -/
def ProperlyEncloses (a b : Arch n) : Prop := a.left < b.left ∧ b.right < a.right

instance (a b : Arch n) : Decidable (a.ProperlyEncloses b) := by
  unfold ProperlyEncloses; infer_instance

/-- `a` and `b` interleave: exactly one endpoint of `b` lies strictly between
the endpoints of `a`. This is the forbidden configuration for a noncrossing
matching. -/
def Crosses (a b : Arch n) : Prop :=
  (a.left < b.left ∧ b.left < a.right ∧ a.right < b.right) ∨
  (b.left < a.left ∧ a.left < b.right ∧ b.right < a.right)

instance (a b : Arch n) : Decidable (a.Crosses b) := by unfold Crosses; infer_instance

@[simp] theorem not_crosses_self (a : Arch n) : ¬ a.Crosses a := by simp [Crosses]

/-- **The noncrossing trichotomy.** Two arches with no common endpoint that do
not cross are separated (one entirely left of the other) or nested (one
strictly inside the other). Every structural fact about noncrossing matchings
is a consequence of this. -/
theorem separated_or_nested (hd : a.DisjointEndpoints b) (hnc : ¬ a.Crosses b) :
    a.right < b.left ∨ b.right < a.left ∨ a.ProperlyEncloses b ∨ b.ProperlyEncloses a := by
  simp only [Crosses, ProperlyEncloses] at hnc ⊢
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hd
  rcases lt_trichotomy a.left b.left with hab | hab | hab
  · by_cases hsep : a.right < b.left
    · exact Or.inl hsep
    · by_cases hnest : b.right < a.right
      · exact Or.inr (Or.inr (Or.inl ⟨hab, hnest⟩))
      · exact absurd (Or.inl ⟨hab, lt_of_le_of_ne (le_of_not_gt hsep) h₃.symm,
          lt_of_le_of_ne (le_of_not_gt hnest) h₄⟩) hnc
  · exact absurd hab h₁
  · by_cases hsep : b.right < a.left
    · exact Or.inr (Or.inl hsep)
    · by_cases hnest : a.right < b.right
      · exact Or.inr (Or.inr (Or.inr ⟨hab, hnest⟩))
      · exact absurd (Or.inr ⟨hab, lt_of_le_of_ne (le_of_not_gt hsep) h₂,
          lt_of_le_of_ne (le_of_not_gt hnest) h₄.symm⟩) hnc

end Arch

end Meanders
