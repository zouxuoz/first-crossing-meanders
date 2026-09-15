import Meanders.Models.FirstCrossing.Surgery.ClosingComponent
import Meanders.Models.FirstCrossing.Interpretation.GraphStep
import Meanders.Models.FirstCrossing.Interpretation.SourceProgress

/-! Physical closing events in an actual source visit and its individual edge substeps. -/

namespace Meanders.FirstCrossing

open SimpleGraph

/-- Away from both endpoints, an added edge changes no degree. -/
theorem degree_sup_edge_away {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {s t v : V}
    (hvs : v ≠ s) (hvt : v ≠ t) : (H ⊔ edge s t).degree v = H.degree v := by
  have he : (H ⊔ edge s t).neighborFinset v = H.neighborFinset v := by
    ext u
    simp [mem_neighborFinset, edge_adj, hvs, hvt]
  exact congrArg Finset.card he

/-- Joining degree-one endpoints removes precisely them from the physical boundary. -/
theorem degree_one_sup_new_edge_iff {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {s t v : V}
    (hst : s ≠ t) (hnew : ¬ H.Adj s t) (hs : H.degree s = 1) (ht : H.degree t = 1) :
    (H ⊔ edge s t).degree v = 1 ↔ H.degree v = 1 ∧ v ≠ s ∧ v ≠ t := by
  by_cases hvs : v = s
  · subst v
    rw [degree_sup_new_edge H hst hnew]
    simp [hs]
  by_cases hvt : v = t
  · subst v
    rw [degree_sup_new_edge_right H hst hnew]
    simp [ht]
  rw [degree_sup_edge_away H hvs hvt]
  simp [hvs, hvt]

/-- Exact physical degree-one coverage propagates through an actual splice,
so owner attachments and FIFO joins need no assumed successor boundary property. -/
theorem spliceJoin_degreeOne {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {w out : Splice} {port : ℕ → V}
    (hm : MateInvariant w.mate) (hd : RepresentsDegreeOne H w.mate port)
    (hinj : Set.InjOn port {i | Live w.mate i}) {x y a b : ℕ}
    (hx : HasMate w.mate x a) (hy : HasMate w.mate y b) (hxy : x ≠ y)
    (hnew : ¬ H.Adj (port x) (port y)) (hjoin : spliceJoin w x y = some out) :
    RepresentsDegreeOne (H ⊔ edge (port x) (port y)) out.mate port := by
  have hphys : port x ≠ port y := fun h => hxy (hinj ⟨a, hx⟩ ⟨b, hy⟩ h)
  have hdx := (hd (port x)).mpr ⟨x, ⟨a, hx⟩, rfl⟩
  have hdy := (hd (port y)).mpr ⟨y, ⟨b, hy⟩, rfl⟩
  have hlive := (spliceJoin_result hm hx hy hxy hjoin).2.1
  intro v
  rw [degree_one_sup_new_edge_iff H hphys hnew hdx hdy, hd v]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hix, hiy⟩
    exact ⟨i, (hlive i).mpr ⟨hi, fun he => hix (congrArg port he),
      fun he => hiy (congrArg port he)⟩, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hi, hix, hiy⟩ := (hlive i).mp hi
    exact ⟨⟨i, hi, rfl⟩, fun he => hix (hinj hi ⟨a, hx⟩ he),
      fun he => hiy (hinj hi ⟨b, hy⟩ he)⟩

/-- Closing a component in a connected source must already complete its entire
physical incidence graph, not merely remove some chosen live endpoints. -/
theorem Source.closing_subgraph_complete {spec : RunSpec} (s : Source spec)
    {H : SimpleGraph (Incidence spec.n)} [DecidableRel H.Adj]
    {mate : List (Option ℕ)} {port : ℕ → Incidence spec.n}
    (hle : H ≤ incidenceGraph s.matchings) (hd : RepresentsDegreeOne H mate port)
    (hp : RepresentsLivePaths mate H port) (hconn : (incidenceGraph s.matchings).Connected)
    {x y : ℕ} (hx : Live mate x) (hy : Live mate y) (hxy : x ≠ y)
    (hreach : H.Reachable (port x) (port y))
    (hedge : (incidenceGraph s.matchings).Adj (port x) (port y))
    (hnew : ¬ H.Adj (port x) (port y)) :
    H ⊔ edge (port x) (port y) = incidenceGraph s.matchings := by
  classical
  let S := Finset.univ.filter fun v =>
    (H ⊔ edge (port x) (port y)).Reachable (port x) v
  have hS : ∀ v, v ∈ S ↔ (H ⊔ edge (port x) (port y)).Reachable (port x) v := by
    simp [S]
  have hs := closing_incidence_component_saturated hle hd hp hx hy hxy
    hreach hedge hnew hS
  have hfull := (closing_incidence_component_permanent hle hd hp hx hy hxy
    hreach hedge hnew hS).2 hconn
  apply le_antisymm (sup_edge_le_of_adj hle hedge)
  intro a b hab
  have ha : a ∈ S := by rw [hfull]; exact Finset.mem_univ _
  rcases (incidenceGraph_adj_iff s.matchings a b).mp hab with rfl | rfl
  · exact (hs a ha).1
  · exact (hs a ha).2

/-- An arbitrary already-added subset of a visit's physical events stays inside
the successor source graph. This permits crossing, attachment, and FIFO substeps. -/
theorem Source.visit_prefix_le_next {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    {E : SimpleGraph (Incidence spec.n)} (hE : E ≤ s.visitEdges hnext) :
    s.partialGraph t ⊔ E ≤ s.partialGraph (t.next side) := by
  rw [s.partialGraph_next ht hnext]
  exact sup_le_sup_left hE _

/-- Any pending physical event is still new after a prefix that has not added it. -/
theorem Source.visit_edge_new_after_prefix {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side))
    {E : SimpleGraph (Incidence spec.n)} {a b : Incidence spec.n}
    (he : (s.visitEdges hnext).Adj a b) (hnot : ¬ E.Adj a b) :
    ¬(s.partialGraph t ⊔ E).Adj a b := by
  intro h
  exact h.elim (s.visitEdges_not_old hnext he) hnot

/-- A closing physical event at any substep of a connected source visit must
complete the whole source, with newness derived from actual event disjointness. -/
theorem Source.visit_closing_complete {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    {E : SimpleGraph (Incidence spec.n)} [DecidableRel E.Adj]
    (hE : E ≤ s.visitEdges hnext) {mate : List (Option ℕ)} {port : ℕ → Incidence spec.n}
    (hd : RepresentsDegreeOne (s.partialGraph t ⊔ E) mate port)
    (hp : RepresentsLivePaths mate (s.partialGraph t ⊔ E) port)
    (hconn : (incidenceGraph s.matchings).Connected)
    {x y : ℕ} (hx : Live mate x) (hy : Live mate y) (hxy : x ≠ y)
    (hreach : (s.partialGraph t ⊔ E).Reachable (port x) (port y))
    (hedge : (s.visitEdges hnext).Adj (port x) (port y))
    (hnot : ¬ E.Adj (port x) (port y)) :
    (s.partialGraph t ⊔ E) ⊔ edge (port x) (port y) = incidenceGraph s.matchings := by
  have hle := (s.visit_prefix_le_next ht hnext hE).trans (s.partialGraph_le _)
  have he := (s.partialGraph_le _) ((s.visitEdges_iff_new ht hnext _ _).mp hedge).1
  exact s.closing_subgraph_complete hle hd hp hconn hx hy hxy hreach he
    (s.visit_edge_new_after_prefix hnext hedge hnot)

/-- A visit with any still-unvisited physical crossing cannot close a component
at its crossing, either owner attachment, or either FIFO substep. -/
theorem Source.visit_no_closure_of_unvisited {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    {E : SimpleGraph (Incidence spec.n)} [DecidableRel E.Adj]
    (hE : E ≤ s.visitEdges hnext) {mate : List (Option ℕ)} {port : ℕ → Incidence spec.n}
    (hd : RepresentsDegreeOne (s.partialGraph t ⊔ E) mate port)
    (hp : RepresentsLivePaths mate (s.partialGraph t ⊔ E) port)
    (hconn : (incidenceGraph s.matchings).Connected)
    {x y : ℕ} (hx : Live mate x) (hy : Live mate y) (hxy : x ≠ y)
    (hedge : (s.visitEdges hnext).Adj (port x) (port y))
    (hnot : ¬ E.Adj (port x) (port y)) {z : Point spec.n}
    (hz : ¬ visited (t.next side) z) :
    ¬(s.partialGraph t ⊔ E).Reachable (port x) (port y) := by
  intro hreach
  have hfull := s.visit_closing_complete ht hnext hE hd hp hconn hx hy hxy
    hreach hedge hnot
  have hstep : (s.partialGraph t ⊔ E) ⊔ edge (port x) (port y) ≤
      s.partialGraph (t.next side) :=
    sup_edge_le_of_adj (s.visit_prefix_le_next ht hnext hE)
      ((s.visitEdges_iff_new ht hnext _ _).mp hedge).1
  have hcross := hstep (hfull.symm ▸ incidenceGraph_crossing s.matchings true z)
  rcases hcross with ⟨_, _, hv⟩ | ⟨ho, _, _⟩
  · exact hz hv
  · cases ho

/-- The concrete number of physical visits discharges the missing-crossing
premise for every substep strictly before the completed source stage. -/
theorem Source.visit_no_closure_before_finish {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (htime : (t.next side).left + (t.next side).right < 2 * spec.n)
    {E : SimpleGraph (Incidence spec.n)} [DecidableRel E.Adj]
    (hE : E ≤ s.visitEdges hnext) {mate : List (Option ℕ)} {port : ℕ → Incidence spec.n}
    (hd : RepresentsDegreeOne (s.partialGraph t ⊔ E) mate port)
    (hp : RepresentsLivePaths mate (s.partialGraph t ⊔ E) port)
    (hconn : (incidenceGraph s.matchings).Connected)
    {x y : ℕ} (hx : Live mate x) (hy : Live mate y) (hxy : x ≠ y)
    (hedge : (s.visitEdges hnext).Adj (port x) (port y))
    (hnot : ¬ E.Adj (port x) (port y)) :
    ¬(s.partialGraph t ⊔ E).Reachable (port x) (port y) := by
  obtain ⟨z, hz⟩ := exists_unvisited_of_progress_lt (t.next side) htime
  exact s.visit_no_closure_of_unvisited ht hnext hE hd hp hconn hx hy hxy hedge hnot hz

/-- Every actual successful attachment or FIFO splice before the last physical
visit keeps the cycle counter unchanged for a connected source. -/
theorem Source.visit_splice_no_cycle_before_finish {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (htime : (t.next side).left + (t.next side).right < 2 * spec.n)
    {E : SimpleGraph (Incidence spec.n)} [DecidableRel E.Adj]
    (hE : E ≤ s.visitEdges hnext) {w out : Splice} {port : ℕ → Incidence spec.n}
    (hm : MateInvariant w.mate) (hd : RepresentsDegreeOne (s.partialGraph t ⊔ E) w.mate port)
    (hp : RepresentsLivePaths w.mate (s.partialGraph t ⊔ E) port)
    (hconn : (incidenceGraph s.matchings).Connected)
    {x y a b : ℕ} (hx : HasMate w.mate x a) (hy : HasMate w.mate y b) (hxy : x ≠ y)
    (hedge : (s.visitEdges hnext).Adj (port x) (port y))
    (hnot : ¬ E.Adj (port x) (port y)) (hj : spliceJoin w x y = some out) :
    out.cycles = w.cycles := by
  have hn := s.visit_no_closure_before_finish ht hnext htime hE hd hp hconn
    ⟨a, hx⟩ ⟨b, hy⟩ hxy hedge hnot
  have hay : a ≠ y := by
    intro he
    subst a
    exact hn ((hp x y ⟨y, hx⟩ ⟨b, hy⟩).mpr (Or.inr hx))
  have hc := (spliceJoin_result hm hx hy hxy hj).2.2.1
  simpa only [ite_eq_right hay, Nat.add_zero] using hc

end Meanders.FirstCrossing
