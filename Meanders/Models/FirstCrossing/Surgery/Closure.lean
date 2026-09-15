import Meanders.Models.FirstCrossing.Original.Incidence
import Meanders.Core.Graph.ClosedSets

/-!
# Permanence of a closed physical component

A processed incidence graph is a subgraph of a completed source diagram.
Once every vertex of a component already has its crossing edge and its
matching edge, no later source edge can attach that component to another.
This is the geometric obstruction used by premature-cycle rejection.
-/

namespace Meanders.FirstCrossing

open SimpleGraph

/-- Saturation means that both *physical* neighbours of each vertex have
already been processed. Component membership is not part of this definition. -/
def SaturatedIncidences {n : Nat}
    (p : NoncrossingMatching n × NoncrossingMatching n)
    (H : SimpleGraph (Incidence n)) (S : Finset (Incidence n)) : Prop :=
  ∀ u ∈ S, H.Adj u (!u.1, u.2) ∧
    H.Adj u (u.1, (ownerMatching p u.1).partner u.2)

/-- In a partial physical graph, degree two already accounts for both possible
physical neighbours, so the component is saturated. -/
theorem saturatedIncidences_of_degree_two {n : Nat}
    {p : NoncrossingMatching n × NoncrossingMatching n}
    {H : SimpleGraph (Incidence n)} [DecidableRel H.Adj]
    {S : Finset (Incidence n)} (hle : H ≤ incidenceGraph p)
    (hdegree : ∀ u ∈ S, H.degree u = 2) : SaturatedIncidences p H S := by
  intro u hu
  have hsub : H.neighborFinset u ⊆ (incidenceGraph p).neighborFinset u := by
    intro v hv
    exact (mem_neighborFinset _ _ _).mpr (hle ((mem_neighborFinset _ _ _).mp hv))
  have he : H.neighborFinset u = (incidenceGraph p).neighborFinset u := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree,
      incidenceGraph_degree, hdegree u hu]
  have hedge {v : Incidence n} (hv : (incidenceGraph p).Adj u v) : H.Adj u v := by
    apply (mem_neighborFinset _ _ _).mp
    rw [he]
    exact (mem_neighborFinset _ _ _).mpr hv
  exact ⟨hedge (incidenceGraph_crossing p u.1 u.2),
    hedge (incidenceGraph_matching p u.1 u.2)⟩

/-- Saturation upgrades closure under processed edges to closure under all
physical edges of the completed source diagram. -/
theorem saturatedIncidences_closed {n : Nat}
    {p : NoncrossingMatching n × NoncrossingMatching n}
    {H : SimpleGraph (Incidence n)} {S : Finset (Incidence n)}
    (hs : SaturatedIncidences p H S)
    (hc : ∀ u v, H.Adj u v → u ∈ S → v ∈ S) :
    ∀ u v, (incidenceGraph p).Adj u v → u ∈ S → v ∈ S := by
  intro u v huv hu
  rcases (incidenceGraph_adj_iff p u v).mp huv with rfl | rfl
  · exact hc u _ (hs u hu).1 hu
  · exact hc u _ (hs u hu).2 hu

/-- A saturated processed component is exactly the same component after any
further subset of the source edges has been processed. -/
theorem saturatedComponent_permanent {n : Nat}
    {p : NoncrossingMatching n × NoncrossingMatching n}
    {H J : SimpleGraph (Incidence n)} {S : Finset (Incidence n)} {root : Incidence n}
    (hs : SaturatedIncidences p H S)
    (hc : ∀ u, u ∈ S ↔ H.Reachable root u)
    (hHJ : H ≤ J) (hJG : J ≤ incidenceGraph p) (u : Incidence n) :
    J.Reachable root u ↔ u ∈ S := by
  have hclosed := saturatedIncidences_closed hs (fun a b hab ha =>
    (hc b).mpr (((hc a).mp ha).trans hab.reachable))
  constructor
  · intro h
    rw [reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact (hc root).mpr (Reachable.refl _)
    | tail _ hadj ih => exact hclosed _ _ (hJG hadj) ih
  · intro hu
    exact ((hc u).mp hu).mono hHJ

/-- A nonempty proper saturated component cannot occur inside a connected
completed overlay. The public connectivity theorem handles rank zero too. -/
theorem saturatedComponent_not_connected {n : Nat}
    {p : NoncrossingMatching n × NoncrossingMatching n}
    {H : SimpleGraph (Incidence n)} {S : Finset (Incidence n)}
    (hs : SaturatedIncidences p H S)
    (hc : ∀ u v, H.Adj u v → u ∈ S → v ∈ S)
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ¬ (unionGraph p).Connected := by
  intro h
  have hg := (incidenceGraph_connected_iff p).mpr h
  have hclosed := saturatedIncidences_closed hs hc
  exact hproper ((connected_iff_closed_finsets (incidenceGraph p)).mp hg |>.2 S hclosed hne)

/-- Concrete premature-cycle criterion: a proper processed component whose
vertices all have degree two rules out a connected source completion. -/
theorem degreeTwoComponent_not_connected {n : Nat}
    {p : NoncrossingMatching n × NoncrossingMatching n}
    {H : SimpleGraph (Incidence n)} [DecidableRel H.Adj]
    {S : Finset (Incidence n)} {root : Incidence n}
    (hle : H ≤ incidenceGraph p)
    (hc : ∀ u, u ∈ S ↔ H.Reachable root u)
    (hdegree : ∀ u ∈ S, H.degree u = 2) (hproper : S ≠ Finset.univ) :
    ¬ (unionGraph p).Connected := by
  apply saturatedComponent_not_connected (saturatedIncidences_of_degree_two hle hdegree)
  · intro u v huv hu
    exact (hc v).mpr (((hc u).mp hu).trans huv.reachable)
  · exact ⟨root, (hc root).mpr (Reachable.refl _)⟩
  · exact hproper

end Meanders.FirstCrossing
