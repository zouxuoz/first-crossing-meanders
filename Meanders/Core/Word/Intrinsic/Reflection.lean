import Meanders.Core.Word.Intrinsic.Height
import Meanders.Core.Word.Splice

namespace Meanders.Dyck

open DyckStep

/-- Exchange open and close steps. -/
def complement : DyckStep → DyckStep
  | U => D
  | D => U

/-- Reverse-complement reflection on an unpointed word. -/
def reverseComplement (w : List DyckStep) : List DyckStep := w.reverse.map complement

@[simp] theorem complement_U : complement U = D := rfl
@[simp] theorem complement_D : complement D = U := rfl
@[simp] theorem complement_complement (s : DyckStep) : complement (complement s) = s := by
  cases s <;> rfl

@[simp] theorem reverseComplement_nil : reverseComplement [] = [] := rfl

@[simp] theorem reverseComplement_cons (s : DyckStep) (w : List DyckStep) :
    reverseComplement (s :: w) = reverseComplement w ++ [complement s] := by
  simp [reverseComplement]

@[simp] theorem reverseComplement_append (a b : List DyckStep) :
    reverseComplement (a ++ b) = reverseComplement b ++ reverseComplement a := by
  simp [reverseComplement, List.reverse_append]

@[simp] theorem reverseComplement_length (w : List DyckStep) :
    (reverseComplement w).length = w.length := by
  simp [reverseComplement]

@[simp] theorem reverseComplement_reverseComplement (w : List DyckStep) :
    reverseComplement (reverseComplement w) = w := by
  induction w with
  | nil => rfl
  | cons s w ih => simp [ih]

@[simp] theorem height_reverseComplement (w : List DyckStep) :
    height (reverseComplement w) = -height w := by
  induction w with
  | nil => simp
  | cons s w ih =>
      rw [reverseComplement_cons, height_append, ih, height_cons]
      cases s <;> simp

theorem take_reverseComplement (w : List DyckStep) (i : Nat) :
    (reverseComplement w).take i = reverseComplement (w.drop (w.length - i)) := by
  rw [reverseComplement, ← List.map_take, List.take_reverse]
  rfl

end Meanders.Dyck

namespace Meanders

open Dyck

/-- Reverse-complement preserves the Dyck predicate. -/
theorem Balanced.reverseComplement {w : List DyckStep} (h : Balanced w) :
    Balanced (reverseComplement w) := by
  rw [balanced_iff_height] at h ⊢
  constructor
  · change Dyck.height (Dyck.reverseComplement w) = 0
    have hz : Dyck.height w = 0 := h.1
    simp [hz]
  · intro i
    rw [← Dyck.height_take, take_reverseComplement, height_reverseComplement]
    have hsum : Dyck.height (w.take (w.length - i)) + Dyck.height (w.drop (w.length - i)) = 0 := by
      rw [← Dyck.height_append, List.take_append_drop]
      exact h.1
    have hp := h.2 (w.length - i)
    rw [← Dyck.height_take] at hp
    omega

end Meanders

