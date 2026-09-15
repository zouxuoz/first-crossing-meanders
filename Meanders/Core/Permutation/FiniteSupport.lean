import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Basic

/-!
Predicates invariant under permutation powers and finite-subtype sums/products. Closed
cycle subsets and Fusion loop colorings share these finite support laws.
-/

namespace Meanders.Permutation

theorem sum_subtype_eq_sum_ite {A R : Type} [Fintype A]
    [AddCommMonoid R] (p : A → Prop) [DecidablePred p] (f : A → R) :
    (∑ x : {x // p x}, f x) = ∑ x : A, if p x then f x else 0 := by
  classical
  let s := {x : A | p x}.toFinset
  calc
    (∑ x : {x // p x}, f x) = ∑ x ∈ s, f x :=
      (Finset.sum_subtype s (fun x => by simp [s]) f).symm
    _ = ∑ x : A, if x ∈ s then f x else 0 := by
      rw [← Finset.sum_filter]
      simp [s]
    _ = ∑ x : A, if p x then f x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      simp [s]

end Meanders.Permutation
