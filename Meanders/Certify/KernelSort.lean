import Mathlib.Data.List.Sort

/-!
# Structurally recursive replay sorting

The evaluator keeps the standard stable merge sort. Kernel replay may use this
fuel-recursive implementation after rewriting by exact equality. The comparison
function is arbitrary: no order laws, row quotient, or alternative tie handling
are assumed. All computational recursion is structural on explicit natural fuel.
-/

namespace Meanders.Certify.KernelSort

/-- Stable merge with structural fuel. The zero-fuel fallback is unreachable
under the explicit combined-length bound used by replay. -/
def merge {α : Type*} (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
    if le x y then x :: merge le fuel xs (y :: ys)
    else y :: merge le fuel (x :: xs) ys

/-- Sufficient fuel reproduces the existing stable merge exactly. -/
theorem merge_eq {α : Type*} (le : α → α → Bool) (fuel : Nat)
    (xs ys : List α) (hf : xs.length + ys.length ≤ fuel) :
    merge le fuel xs ys = List.merge xs ys le := by
  induction fuel generalizing xs ys with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    subst ys
    simp [merge]
  | succ fuel ih =>
    cases xs with
    | nil => simp [merge]
    | cons x xs =>
      cases ys with
      | nil => simp [merge]
      | cons y ys =>
        rw [merge, List.merge]
        split
        · rw [ih xs (y :: ys) (by simp only [List.length_cons] at hf ⊢; omega)]
        · rw [ih (x :: xs) ys (by simp only [List.length_cons] at hf ⊢; omega)]

/-- The same contiguous ceil/floor split as the standard stable merge sort. -/
def sortAux {α : Type*} (le : α → α → Bool) : Nat → List α → List α
  | 0, xs => xs
  | _ + 1, [] => []
  | _ + 1, [a] => [a]
  | fuel + 1, a :: b :: xs =>
    let input := a :: b :: xs
    let split := (input.length + 1) / 2
    let left := sortAux le fuel (input.take split)
    let right := sortAux le fuel (input.drop split)
    merge le (left.length + right.length) left right

/-- Fuel at least the input length gives exact standard merge-sort output. -/
theorem sortAux_eq {α : Type*} (le : α → α → Bool) (fuel : Nat)
    (xs : List α) (hf : xs.length ≤ fuel) : sortAux le fuel xs = xs.mergeSort le := by
  induction fuel generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    simp [sortAux]
  | succ fuel ih =>
    cases xs with
    | nil => simp [sortAux]
    | cons a xs =>
      cases xs with
      | nil => simp [sortAux]
      | cons b xs =>
        rw [sortAux, merge_eq _ _ _ _ le_rfl, List.mergeSort]
        simp only [List.MergeSort.Internal.splitInTwo_fst,
          List.MergeSort.Internal.splitInTwo_snd]
        rw [ih _ (by simp only [List.length_take, List.length_cons] at hf ⊢; omega),
          ih _ (by simp only [List.length_drop, List.length_cons] at hf ⊢; omega)]

/-- Kernel-reducible replay sort with precisely the required fuel. -/
def sort {α : Type*} (xs : List α) (le : α → α → Bool) : List α := sortAux le xs.length xs

/-- Replay may rewrite the unchanged evaluator sort by this equality. -/
theorem sort_eq {α : Type*} (xs : List α) (le : α → α → Bool) :
    sort xs le = xs.mergeSort le := sortAux_eq le xs.length xs le_rfl

end Meanders.Certify.KernelSort
