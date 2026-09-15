import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Basic

/-! Finite graph connectivity characterized by adjacency-closed vertex sets. -/

namespace SimpleGraph

/-- A finite graph is connected exactly when every nonempty adjacency-closed
vertex set is the whole boundary, and the boundary itself is nonempty. -/
theorem connected_iff_closed_finsets {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    G.Connected ↔ Nonempty V ∧
      ∀ S : Finset V, (∀ u v, G.Adj u v → u ∈ S → v ∈ S) →
        S.Nonempty → S = Finset.univ := by
  classical
  constructor
  · intro h
    refine ⟨h.nonempty, fun S hS ⟨u, hu⟩ => Finset.eq_univ_of_forall fun v => ?_⟩
    obtain ⟨p⟩ := h u v
    induction p with
    | nil => exact hu
    | @cons u w v huw p ih => exact ih (hS u w huw hu)
  · rintro ⟨hn, h⟩
    let : Nonempty V := hn
    refine ⟨fun u v => ?_⟩
    let S : Finset V := Finset.univ.filter (G.Reachable u)
    have he : S = Finset.univ := h S (by
      intro a b hab ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp ha).2.trans hab.reachable⟩) (by
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, .rfl⟩⟩)
    exact (Finset.mem_filter.mp (show v ∈ S from he ▸ Finset.mem_univ v)).2

end SimpleGraph
