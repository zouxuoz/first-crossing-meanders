import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Parity

/-! A finite set closed under a fixed-point-free pairing has even cardinality. -/

namespace Meanders

/-- Split a pairing into its smaller and larger endpoints. -/
theorem even_card_of_pairing {V : Type*} [LinearOrder V] (s : Finset V) (f : V → V)
    (hin : ∀ v ∈ s, f v ∈ s) (hinv : ∀ v ∈ s, f (f v) = v)
    (hne : ∀ v ∈ s, f v ≠ v) : Even s.card := by
  have hcards : (s.filter fun v => v < f v).card = (s.filter fun v => ¬v < f v).card := by
    apply Finset.card_bij (fun v _ => f v)
    · intro v hv
      simp only [Finset.mem_filter] at hv ⊢
      exact ⟨hin v hv.1, by rw [hinv v hv.1]; exact not_lt_of_gt hv.2⟩
    · intro v hv w hw he
      have hv' := (Finset.mem_filter.mp hv).1
      have hw' := (Finset.mem_filter.mp hw).1
      simpa [hinv v hv', hinv w hw'] using congrArg f he
    · intro v hv
      simp only [Finset.mem_filter] at hv
      refine ⟨f v, Finset.mem_filter.mpr ⟨hin v hv.1, ?_⟩, hinv v hv.1⟩
      rw [hinv v hv.1]
      exact lt_of_le_of_ne (le_of_not_gt hv.2) (hne v hv.1)
  have hsum := Finset.card_filter_add_card_filter_not (s := s) (p := fun v => v < f v)
  exact ⟨(s.filter fun v => v < f v).card, by omega⟩

end Meanders
