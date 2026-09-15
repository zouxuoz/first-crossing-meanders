import Meanders.Core.Graph.Flood
import Meanders.Core.Matching

/-!
# The overlay of two matchings

Superimposing two noncrossing perfect matchings on the same `2n` points gives
a graph in which every vertex has degree one or two: `unionGraph`. Every
meander problem is a connectivity condition on such an overlay: a closed
meander is a pair whose union graph is connected (`Meanders.Problems.Closed`),
and the open-meander problem is the same overlay with unmatched points. That
is why this file is Core rather than part of any one problem.

`isConnectedUnion` is the computable form of the connectivity condition: the
flood fill of `Meanders.Core.Graph.Flood` run from point `0` with the two
partner maps as neighbourhoods, so one step costs `O(1)` per vertex.
`isConnectedUnion_iff` is the proof that it decides `(unionGraph p).Connected`.
It lives here rather than with the counting algorithms because it is a
decision procedure for a predicate of the semantics, not a way of counting.
-/

namespace Meanders

open SimpleGraph

variable {n : ℕ}

/-- Superimpose two matchings on the same boundary: join each point to its
partner in each of them. Every vertex has degree one (when the two partners
coincide) or two. -/
def unionGraph (p : NoncrossingMatching n × NoncrossingMatching n) : SimpleGraph (Point n) :=
  SimpleGraph.fromRel fun u v => p.1.partner u = v ∨ p.2.partner u = v

/-- Two points are joined exactly when one is the partner of the other in at
least one of the two matchings. (`fromRel` symmetrises, but `partner` is an
involution, so the symmetrised relation is the original one.) -/
theorem unionGraph_adj (p : NoncrossingMatching n × NoncrossingMatching n) (u v : Point n) :
    (unionGraph p).Adj u v ↔ u ≠ v ∧ (p.1.partner u = v ∨ p.2.partner u = v) := by
  rw [unionGraph, SimpleGraph.fromRel_adj]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Or.inl h⟩
  rcases h with (h | h) | (h | h)
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl (by rw [← h, p.1.partner_partner])
  · exact Or.inr (by rw [← h, p.2.partner_partner])

instance (p : NoncrossingMatching n × NoncrossingMatching n) : DecidableRel (unionGraph p).Adj :=
  fun u v => decidable_of_iff _ (unionGraph_adj p u v).symm

/-- The neighbours of `v` in the union graph: its two partners. -/
def unionNbr (p : NoncrossingMatching n × NoncrossingMatching n) (v : Point n) : Finset (Point n) :=
  {p.1.partner v, p.2.partner v}

theorem isNeighbourFn_unionNbr (p : NoncrossingMatching n × NoncrossingMatching n) :
    IsNeighbourFn (unionGraph p) (unionNbr p) := by
  intro v u
  rw [unionGraph_adj, unionNbr]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    exacts [⟨(p.1.partner_ne v).symm, Or.inl rfl⟩, ⟨(p.2.partner_ne v).symm, Or.inr rfl⟩]
  · rintro ⟨-, rfl | rfl⟩
    exacts [Or.inl rfl, Or.inr rfl]

/-- The computable connectivity test used by `countClosedMeanders`: flood from
point `0`. Order `0` has no points at all, so nothing is connected there. -/
def isConnectedUnion (p : NoncrossingMatching n × NoncrossingMatching n) : Bool :=
  if h : 0 < 2 * n then reachFinset (unionNbr p) ⟨0, h⟩ = Finset.univ else false

theorem isConnectedUnion_iff (p : NoncrossingMatching n × NoncrossingMatching n) :
    isConnectedUnion p = true ↔ (unionGraph p).Connected := by
  unfold isConnectedUnion
  split
  · rename_i h
    simpa using (connected_iff_reachFinset (isNeighbourFn_unionNbr p) ⟨0, h⟩).symm
  · rename_i h
    simp only [Bool.false_eq_true, false_iff]
    intro hc
    obtain ⟨v⟩ := hc.2
    exact absurd v.isLt (by omega)

end Meanders

