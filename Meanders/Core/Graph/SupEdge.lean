import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Reachability after adding one edge

Adding the edge `{s, t}` to `G` joins two vertices exactly when they were
already joined, or one reaches `s` and the other `t`. This is the whole
graph theory behind the folded transfer: each step of the scan adds one
rainbow arch and at most two bottom arches, and the state records which open
ends are joined.
-/

namespace Meanders

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {s t u v : V}

theorem reachable_sup_edge_iff :
    (G ⊔ edge s t).Reachable u v ↔
      G.Reachable u v ∨
        (G.Reachable u s ∧ G.Reachable t v) ∨ (G.Reachable u t ∧ G.Reachable s v) := by
  constructor
  · intro h
    rw [reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Or.inl (Reachable.refl _)
    | tail _ hadj ih =>
      rename_i x y
      rcases (sup_adj _ _ _ _).1 hadj with hG | hE
      · rcases ih with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact Or.inl (h.trans hG.reachable)
        · exact Or.inr (Or.inl ⟨h₁, h₂.trans hG.reachable⟩)
        · exact Or.inr (Or.inr ⟨h₁, h₂.trans hG.reachable⟩)
      · rw [edge_adj] at hE
        obtain ⟨hxy, -⟩ := hE
        rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · rw [hy]; rw [hx] at ih
          rcases ih with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · exact Or.inr (Or.inl ⟨h, Reachable.refl _⟩)
          · exact Or.inr (Or.inl ⟨h₁, Reachable.refl _⟩)
          · exact Or.inl h₁
        · rw [hy]; rw [hx] at ih
          rcases ih with h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · exact Or.inr (Or.inr ⟨h, Reachable.refl _⟩)
          · exact Or.inl h₁
          · exact Or.inr (Or.inr ⟨h₁, Reachable.refl _⟩)
  · have hmono : G.Reachable ≤ (G ⊔ edge s t).Reachable := Reachable.mono' le_sup_left
    rintro (h | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact hmono _ _ h
    · by_cases hst : s = t
      · subst hst; exact hmono _ _ (h₁.trans h₂)
      · have hadj : (G ⊔ edge s t).Adj s t :=
          (sup_adj _ _ _ _).2 (Or.inr ((edge_adj _ _ _ _).2 ⟨Or.inl ⟨rfl, rfl⟩, hst⟩))
        exact (hmono _ _ h₁).trans (hadj.reachable.trans (hmono _ _ h₂))
    · by_cases hst : s = t
      · subst hst; exact hmono _ _ (h₁.trans h₂)
      · have hadj : (G ⊔ edge s t).Adj t s :=
          (sup_adj _ _ _ _).2
            (Or.inr ((edge_adj _ _ _ _).2 ⟨Or.inr ⟨rfl, rfl⟩, Ne.symm hst⟩))
        exact (hmono _ _ h₁).trans (hadj.reachable.trans (hmono _ _ h₂))

/-- Adding an edge between two isolated vertices joins exactly those two. -/
theorem reachable_sup_edge_isolated {l r u v : V}
    (hl : ∀ w, G.Reachable l w ↔ w = l) (hr : ∀ w, G.Reachable r w ↔ w = r) :
    (G ⊔ edge l r).Reachable u v ↔
      G.Reachable u v ∨ (u = l ∧ v = r) ∨ (u = r ∧ v = l) := by
  rw [reachable_sup_edge_iff]
  constructor
  · rintro (huv | ⟨hul, hrv⟩ | ⟨hur, hlv⟩)
    · exact Or.inl huv
    · rw [reachable_comm, hl] at hul
      rw [hr] at hrv
      exact Or.inr (Or.inl ⟨hul, hrv⟩)
    · rw [reachable_comm, hr] at hur
      rw [hl] at hlv
      exact Or.inr (Or.inr ⟨hur, hlv⟩)
  · rintro (huv | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl huv
    · exact Or.inr (Or.inl ⟨Reachable.refl _, Reachable.refl _⟩)
    · exact Or.inr (Or.inr ⟨Reachable.refl _, Reachable.refl _⟩)

end Meanders
