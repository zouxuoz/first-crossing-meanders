import Meanders.Core.Word.Balanced

namespace Meanders.Dyck

open DyckStep

/-- Signed path height of a list of steps. -/
def height (w : List DyckStep) : Int := Meanders.height w w.length

theorem height_eq_count (w : List DyckStep) :
    height w = (w.count U : Int) - (w.count D : Int) := by
  simp [height, Meanders.height]

/-- Whole-word height of a prefix is the shared prefix-height function. -/
theorem height_take (w : List DyckStep) (i : Nat) :
    height (w.take i) = Meanders.height w i := height_eq_count _

@[simp] theorem height_nil : height [] = 0 := rfl
@[simp] theorem height_cons (s : DyckStep) (w : List DyckStep) :
    height (s :: w) = stepHeight s + height w := by
  cases s <;> simp [height, Meanders.height, stepHeight] <;> ring

@[simp] theorem height_append (a b : List DyckStep) :
    height (a ++ b) = height a + height b := by
  simp only [height_eq_count, List.count_append, Nat.cast_add]
  ring

@[simp] theorem stepHeight_U : stepHeight U = 1 := rfl
@[simp] theorem stepHeight_D : stepHeight D = -1 := rfl

end Meanders.Dyck

namespace Meanders

open DyckStep

theorem Balanced.height_nonneg_take {w : List DyckStep} (h : Balanced w) (i : Nat) :
    0 ≤ Dyck.height (w.take i) := by
  rw [Dyck.height_take]
  exact h.height_nonneg i

end Meanders
