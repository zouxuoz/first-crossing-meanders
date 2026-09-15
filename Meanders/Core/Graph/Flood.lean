import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# A flood fill that decides connectivity

`SimpleGraph.Connected` is already decidable in Mathlib for a finite graph,
but that instance enumerates walks and is far too slow to count anything with.
This file is a general-purpose replacement: `closureIter` floods outwards from
a vertex, and `connected_iff_reachFinset` proves the flood fills the graph
exactly when the graph is connected.

Two details make the flood fast. It takes the neighbourhoods as a *function*
`nbr` rather than filtering all of `V` at every step, so a graph of bounded
degree costs `O(1)` per vertex per round instead of `O(|V|)`. And it stops as
soon as a round adds nothing, which is what keeps disconnected graphs cheap.

Nothing here knows about meanders: `V` is any finite type with decidable
equality, and `IsNeighbourFn` is the only link to the graph.
-/

namespace Meanders

open SimpleGraph

section Flood

variable {V : Type*} [DecidableEq V]

/-- `nbr` lists the neighbours of each vertex of `G`. -/
def IsNeighbourFn (G : SimpleGraph V) (nbr : V → Finset V) : Prop :=
  ∀ v u, u ∈ nbr v ↔ G.Adj v u

/-- Add every neighbour of every vertex of `S`. -/
def closureStep (nbr : V → Finset V) (S : Finset V) : Finset V := S ∪ S.biUnion nbr

theorem subset_closureStep (nbr : V → Finset V) (S : Finset V) : S ⊆ closureStep nbr S :=
  Finset.subset_union_left

theorem mem_closureStep_of_mem_nbr {nbr : V → Finset V} {S : Finset V} {v u : V}
    (hv : v ∈ S) (h : u ∈ nbr v) : u ∈ closureStep nbr S :=
  Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨v, hv, h⟩)

/-- Flood for at most `k` rounds, stopping early once a round adds nothing. -/
def closureIter (nbr : V → Finset V) (S : Finset V) : ℕ → Finset V
  | 0 => S
  | k + 1 => if closureStep nbr S = S then S else closureIter nbr (closureStep nbr S) k

theorem closureIter_succ_of_fixed {nbr : V → Finset V} {S : Finset V}
    (h : closureStep nbr S = S) (k : ℕ) : closureIter nbr S k = S := by
  cases k with
  | zero => rfl
  | succ k => rw [closureIter, ite_eq_left h]

theorem subset_closureIter (nbr : V → Finset V) (S : Finset V) (k : ℕ) :
    S ⊆ closureIter nbr S k := by
  induction k generalizing S with
  | zero => exact Finset.Subset.refl _
  | succ k ih =>
    rw [closureIter]
    split
    · exact Finset.Subset.refl _
    · exact (subset_closureStep nbr S).trans (ih (closureStep nbr S))

theorem reachable_of_mem_closureIter {G : SimpleGraph V} {nbr : V → Finset V}
    (hnbr : IsNeighbourFn G nbr) {S : Finset V} {k : ℕ} {u : V}
    (h : u ∈ closureIter nbr S k) : ∃ v ∈ S, G.Reachable v u := by
  induction k generalizing S with
  | zero => exact ⟨u, h, SimpleGraph.Reachable.refl u⟩
  | succ k ih =>
    rw [closureIter] at h
    split at h
    · exact ⟨u, h, SimpleGraph.Reachable.refl u⟩
    · obtain ⟨w, hw, hru⟩ := ih h
      rcases Finset.mem_union.1 hw with hw | hw
      · exact ⟨w, hw, hru⟩
      · obtain ⟨v, hv, hadj⟩ := Finset.mem_biUnion.1 hw
        exact ⟨v, hv, (SimpleGraph.Adj.reachable ((hnbr v w).1 hadj)).trans hru⟩

theorem mem_closureIter_of_walk {G : SimpleGraph V} {nbr : V → Finset V}
    (hnbr : IsNeighbourFn G nbr) {S : Finset V} {v u : V} (hv : v ∈ S) (p : G.Walk v u)
    {k : ℕ} (hk : p.length ≤ k) : u ∈ closureIter nbr S k := by
  induction p generalizing S k with
  | nil => exact subset_closureIter nbr S k hv
  | cons hadj q ih =>
    rename_i x _
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hx : x ∈ closureStep nbr S := mem_closureStep_of_mem_nbr hv ((hnbr _ _).2 hadj)
    rw [closureIter]
    split
    · rename_i hfix
      rw [hfix] at hx
      have := ih hx (k := k) (by simp at hk; omega)
      rwa [closureIter_succ_of_fixed hfix] at this
    · exact ih hx (by simp at hk; omega)

variable [Fintype V]

/-- The set of vertices reachable from `v`, computed by flooding. -/
def reachFinset (nbr : V → Finset V) (v : V) : Finset V :=
  closureIter nbr {v} (Fintype.card V)

theorem mem_reachFinset_iff {G : SimpleGraph V} {nbr : V → Finset V}
    (hnbr : IsNeighbourFn G nbr) (v u : V) : u ∈ reachFinset nbr v ↔ G.Reachable v u := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨w, hw, hr⟩ := reachable_of_mem_closureIter hnbr h
    rwa [Finset.mem_singleton.1 hw] at hr
  · refine h.elim_path fun p => ?_
    exact mem_closureIter_of_walk hnbr (Finset.mem_singleton_self v) p.1
      (le_of_lt p.isPath.length_lt)

/-- **The flood test is exactly connectivity.** -/
theorem connected_iff_reachFinset {G : SimpleGraph V} {nbr : V → Finset V}
    (hnbr : IsNeighbourFn G nbr) (v : V) : G.Connected ↔ reachFinset nbr v = Finset.univ := by
  refine ⟨fun h => Finset.eq_univ_of_forall fun u =>
      (mem_reachFinset_iff hnbr v u).2 (h.1 v u), fun h => ?_⟩
  have : Nonempty V := ⟨v⟩
  refine ⟨fun u u' => ?_⟩
  have hu : G.Reachable v u := (mem_reachFinset_iff hnbr v u).1 (h ▸ Finset.mem_univ u)
  have hu' : G.Reachable v u' := (mem_reachFinset_iff hnbr v u').1 (h ▸ Finset.mem_univ u')
  exact hu.symm.trans hu'

end Flood

end Meanders
