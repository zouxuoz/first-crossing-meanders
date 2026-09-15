import Meanders.Core.Word.Partner

/-!
# Balanced words without a fixed semilength

`Balanced` is the existing `IsDyck` predicate with the semilength read from
its word. It is useful when an active boundary grows and shrinks during a scan.
-/

namespace Meanders

open DyckStep

/-- A Dyck word of any semilength, on the existing list representation. -/
def Balanced (w : List DyckStep) : Prop := IsDyck (w.length / 2) w

instance (w : List DyckStep) : Decidable (Balanced w) := inferInstanceAs (Decidable (IsDyck _ w))

theorem Balanced.of_isDyck {n : ℕ} {w : List DyckStep} (h : IsDyck n w) : Balanced w := by
  have hn : w.length / 2 = n := by rw [h.length]; omega
  rwa [Balanced, hn]

theorem balanced_iff (w : List DyckStep) :
    Balanced w ↔ w.count U = w.count D ∧ ∀ i, (w.take i).count D ≤ (w.take i).count U := by
  constructor
  · intro h
    exact ⟨h.toDyckWord.count_U_eq_count_D, h.toDyckWord.count_D_le_count_U⟩
  · rintro ⟨hb, hp⟩
    exact Balanced.of_isDyck (isDyck_of_dyckWord (⟨w, hb, hp⟩ : DyckWord) rfl)

theorem Balanced.count_eq {w : List DyckStep} (h : Balanced w) : w.count U = w.count D :=
  (balanced_iff w).mp h |>.1

theorem Balanced.prefix {w : List DyckStep} (h : Balanced w) (i : ℕ) :
    (w.take i).count D ≤ (w.take i).count U := (balanced_iff w).mp h |>.2 i

@[simp] theorem balanced_nil : Balanced [] := by simp [balanced_iff]

/-- The unoriented pairing relation of a word. -/
def Partners (w : List DyckStep) (i j : ℕ) : Prop := Paired w i j ∨ Paired w j i

namespace Partners

variable {w : List DyckStep} {i j k : ℕ}

theorem symm (h : Partners w i j) : Partners w j i := h.elim Or.inr Or.inl

theorem ne (h : Partners w i j) : i ≠ j := by
  rcases h with h | h
  · exact ne_of_lt h.lt
  · exact ne_of_gt h.lt

theorem unique (h : Partners w i j) (h' : Partners w i k) : j = k := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact h.right_unique h'
  · have he := h.isU.symm.trans h'.isD
    cases he
  · have he := h.isD.symm.trans h'.isU
    cases he
  · exact h.left_unique h'

end Partners

end Meanders
