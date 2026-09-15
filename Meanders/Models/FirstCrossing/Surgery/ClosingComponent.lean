import Meanders.Models.FirstCrossing.Surgery.Splice
import Meanders.Models.FirstCrossing.Surgery.Closure
import Meanders.Models.FirstCrossing.Surgery.Cup
import Meanders.Models.FirstCrossing.Surgery.Coverage

/-! A physical closing splice saturates its entire processed component. -/

namespace Meanders.FirstCrossing

open SimpleGraph

/-- The frontier represents exactly the degree-one physical vertices. -/
def RepresentsDegreeOne {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (mate : List (Option ℕ)) (port : ℕ → V) : Prop :=
  ∀ v, H.degree v = 1 ↔ ∃ i, Live mate i ∧ port i = v

/-- Adding a genuinely new edge increases the degree at its endpoint by one. -/
theorem degree_sup_new_edge {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {s t : V}
    (hst : s ≠ t) (hnew : ¬ H.Adj s t) :
    (H ⊔ edge s t).degree s = H.degree s + 1 := by
  have he : (H ⊔ edge s t).neighborFinset s = insert t (H.neighborFinset s) := by
    ext v
    simp only [mem_neighborFinset, sup_adj, edge_adj, Finset.mem_insert]
    aesop
  rw [← card_neighborFinset_eq_degree, he, Finset.card_insert_of_notMem,
    card_neighborFinset_eq_degree]
  simpa using hnew

/-- The other endpoint has the same exact degree increment. -/
theorem degree_sup_new_edge_right {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {s t : V}
    (hst : s ≠ t) (hnew : ¬ H.Adj s t) :
    (H ⊔ edge s t).degree t = H.degree t + 1 := by
  have he : (H ⊔ edge s t).neighborFinset t = insert s (H.neighborFinset t) := by
    ext v
    simp only [mem_neighborFinset, sup_adj, edge_adj, Finset.mem_insert]
    aesop
  rw [← card_neighborFinset_eq_degree, he, Finset.card_insert_of_notMem,
    card_neighborFinset_eq_degree]
  simpa only [mem_neighborFinset, adj_comm] using hnew

/-- Adding an edge inside one existing component does not change any reachability. -/
theorem reachable_sup_internal_edge {V : Type*} {H : SimpleGraph V} {s t u v : V}
    (hst : H.Reachable s t) : (H ⊔ edge s t).Reachable u v ↔ H.Reachable u v := by
  rw [Meanders.reachable_sup_edge_iff]
  constructor
  · rintro (h | ⟨hus, htv⟩ | ⟨hut, hsv⟩)
    · exact h
    · exact hus.trans (hst.trans htv)
    · exact hut.trans (hst.symm.trans hsv)
  · exact Or.inl

/-- An edge of the completed graph remains within its graph when added to a partial graph. -/
theorem sup_edge_le_of_adj {V : Type*} {H F : SimpleGraph V} {s t : V}
    (hle : H ≤ F) (hadj : F.Adj s t) : H ⊔ edge s t ≤ F := by
  apply sup_le hle
  intro u v huv
  rcases (edge_adj _ _ _ _).mp huv with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩
  · exact hadj
  · exact hadj.symm

/-- A closing edge saturates every vertex of its processed component. The proof
uses exact degree-one frontier coverage, rather than a desired output degree. -/
theorem closing_component_degree_two {V : Type*} [Fintype V] [DecidableEq V]
    {H F : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel F.Adj]
    {mate : List (Option ℕ)} {port : ℕ → V} (hle : H ≤ F)
    (hF : ∀ v, F.degree v = 2) (hd : RepresentsDegreeOne H mate port)
    (hp : RepresentsLivePaths mate H port) {x y : ℕ}
    (hx : Live mate x) (hy : Live mate y) (hxy : x ≠ y)
    (hreach : H.Reachable (port x) (port y)) (hedge : F.Adj (port x) (port y))
    (hnew : ¬ H.Adj (port x) (port y)) {v : V}
    (hv : (H ⊔ edge (port x) (port y)).Reachable (port x) v) :
    (H ⊔ edge (port x) (port y)).degree v = 2 := by
  have hJle := sup_edge_le_of_adj hle hedge
  have hupper : (H ⊔ edge (port x) (port y)).degree v ≤ 2 := by
    simpa [hF v] using (H ⊔ edge (port x) (port y)).degree_le_of_le hJle (v := v)
  have hmono : H.degree v ≤ (H ⊔ edge (port x) (port y)).degree v :=
    H.degree_le_of_le le_sup_left
  have hdx : H.degree (port x) = 1 := (hd _).mpr ⟨x, hx, rfl⟩
  have hdy : H.degree (port y) = 1 := (hd _).mpr ⟨y, hy, rfl⟩
  have hvold := (reachable_sup_internal_edge hreach).mp hv
  have hpos : 0 < H.degree v := by
    by_cases he : port x = v
    · rw [← he, hdx]
      decide
    · exact hvold.degree_pos_right he
  by_cases hvone : H.degree v = 1
  · obtain ⟨i, hi, hiv⟩ := (hd v).mp hvone
    have hmxy : HasMate mate x y := ((hp x y hx hy).mp hreach).resolve_left hxy
    have hxi := (hp x i hx hi).mp (hiv ▸ hvold)
    rcases hxi with rfl | hxi
    · subst v
      rw [degree_sup_new_edge H hedge.ne hnew, hdx]
    · have hie : i = y := hxi.unique hmxy
      subst i
      subst v
      rw [degree_sup_new_edge_right H hedge.ne hnew, hdy]
  · omega

/-- In the physical incidence graph, a closing component has both possible source
edges at every vertex, as required by the existing permanence theorem. -/
theorem closing_incidence_component_saturated {n : ℕ}
    {p : NoncrossingMatching n × NoncrossingMatching n}
    {H : SimpleGraph (Incidence n)} [DecidableRel H.Adj]
    {mate : List (Option ℕ)} {port : ℕ → Incidence n}
    (hle : H ≤ incidenceGraph p) (hd : RepresentsDegreeOne H mate port)
    (hp : RepresentsLivePaths mate H port) {x y : ℕ}
    (hx : Live mate x) (hy : Live mate y) (hxy : x ≠ y)
    (hreach : H.Reachable (port x) (port y))
    (hedge : (incidenceGraph p).Adj (port x) (port y))
    (hnew : ¬ H.Adj (port x) (port y)) {S : Finset (Incidence n)}
    (hS : ∀ v, v ∈ S ↔ (H ⊔ edge (port x) (port y)).Reachable (port x) v) :
    SaturatedIncidences p (H ⊔ edge (port x) (port y)) S := by
  apply saturatedIncidences_of_degree_two (sup_edge_le_of_adj hle hedge)
  intro v hv
  exact closing_component_degree_two hle (incidenceGraph_degree p) hd hp hx hy hxy
    hreach hedge hnew ((hS v).mp hv)

/-- The actual component formed by closing an incidence path is permanent in every
source subgraph extension, and a connected source forces it to span all vertices. -/
theorem closing_incidence_component_permanent {n : ℕ}
    {p : NoncrossingMatching n × NoncrossingMatching n}
    {H : SimpleGraph (Incidence n)} [DecidableRel H.Adj]
    {mate : List (Option ℕ)} {port : ℕ → Incidence n}
    (hle : H ≤ incidenceGraph p) (hd : RepresentsDegreeOne H mate port)
    (hp : RepresentsLivePaths mate H port) {x y : ℕ}
    (hx : Live mate x) (hy : Live mate y) (hxy : x ≠ y)
    (hreach : H.Reachable (port x) (port y))
    (hedge : (incidenceGraph p).Adj (port x) (port y))
    (hnew : ¬ H.Adj (port x) (port y)) {S : Finset (Incidence n)}
    (hS : ∀ v, v ∈ S ↔ (H ⊔ edge (port x) (port y)).Reachable (port x) v) :
    (∀ J : SimpleGraph (Incidence n), H ⊔ edge (port x) (port y) ≤ J →
      J ≤ incidenceGraph p → ∀ v, J.Reachable (port x) v ↔ v ∈ S) ∧
      ((incidenceGraph p).Connected → S = Finset.univ) := by
  have hs := closing_incidence_component_saturated hle hd hp hx hy hxy
    hreach hedge hnew hS
  constructor
  · intro J hHJ hJG v
    exact saturatedComponent_permanent hs hS hHJ hJG v
  · intro hconn
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    exact (saturatedComponent_permanent hs hS (sup_edge_le_of_adj hle hedge)
      le_rfl v).mp (hconn.preconnected (port x) v)

end Meanders.FirstCrossing

/-!
# Degree and coverage at a fresh physical cup

The two fresh isolated physical vertices become exactly two new degree-one
vertices. Existing live names and completed-component witnesses keep their
physical meanings. All statements refer to the actual appended mate entries.
-/

namespace Meanders.FirstCrossing

open SimpleGraph

/-- The new physical cup creates exactly two additional degree-one vertices. -/
theorem appendCup_degreeOne {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {mate : List (Option Nat)} {port : Nat → V}
    (hd : RepresentsDegreeOne H mate port)
    (hne : port mate.length ≠ port (mate.length + 1))
    (h0 : H.degree (port mate.length) = 0)
    (h1 : H.degree (port (mate.length + 1)) = 0) :
    RepresentsDegreeOne (H ⊔ edge (port mate.length) (port (mate.length + 1)))
      (mate ++ [some (mate.length + 1), some mate.length]) port := by
  have hnew : ¬ H.Adj (port mate.length) (port (mate.length + 1)) := by
    intro ha
    have hp := (H.degree_pos_iff_exists_adj _).mpr ⟨_, ha⟩
    omega
  intro v
  by_cases hv0 : v = port mate.length
  · subst v
    rw [degree_sup_new_edge H hne hnew, h0]
    exact iff_of_true (by decide) ⟨mate.length,
      (appendCup_live mate _).mpr (Or.inr (Or.inl rfl)), rfl⟩
  by_cases hv1 : v = port (mate.length + 1)
  · subst v
    rw [degree_sup_new_edge_right H hne hnew, h1]
    exact iff_of_true (by decide) ⟨mate.length + 1,
      (appendCup_live mate _).mpr (Or.inr (Or.inr rfl)), rfl⟩
  have hneighbors : (H ⊔ edge (port mate.length) (port (mate.length + 1))).neighborFinset v =
      H.neighborFinset v := by
    ext u
    simp only [mem_neighborFinset, sup_adj, edge_adj]
    aesop
  have hdegree : (H ⊔ edge (port mate.length) (port (mate.length + 1))).degree v =
      H.degree v := by
    rw [← card_neighborFinset_eq_degree, hneighbors, card_neighborFinset_eq_degree]
  rw [hdegree, hd]
  constructor
  · rintro ⟨i, hi, hiv⟩
    exact ⟨i, (appendCup_live mate i).mpr (Or.inl hi), hiv⟩
  · rintro ⟨i, hi, hiv⟩
    rcases (appendCup_live mate i).mp hi with hi | rfl | rfl
    · exact ⟨i, hi, hiv⟩
    · exact False.elim (hv0 hiv.symm)
    · exact False.elim (hv1 hiv.symm)

/-- The actual candidate array has the same degree-one interpretation. -/
theorem candidateCup_degreeOne {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {mate : List Nat} {port : Nat → V}
    (hd : RepresentsDegreeOne H (mate.map some) port)
    (hne : port mate.length ≠ port (mate.length + 1))
    (h0 : H.degree (port mate.length) = 0)
    (h1 : H.degree (port (mate.length + 1)) = 0) :
    RepresentsDegreeOne (H ⊔ edge (port mate.length) (port (mate.length + 1)))
      (mate.map some ++ [some (mate.length + 1), some mate.length]) port := by
  simpa only [List.length_map] using appendCup_degreeOne hd
    (by simpa only [List.length_map] using hne)
    (by rw [List.length_map]; exact h0)
    (by rw [List.length_map]; exact h1)

/-- Adding the cup extends processed-vertex coverage by exactly its fresh
physical endpoints and leaves the closed-component witness list unchanged. -/
theorem appendCup_covers {V : Type*} {H : SimpleGraph V}
    {mate : List (Option Nat)} {port : Nat → V} {closed : List V} {processed : V → Prop}
    (hc : CoversProcessed mate H port closed processed) :
    CoversProcessed (mate ++ [some (mate.length + 1), some mate.length])
      (H ⊔ edge (port mate.length) (port (mate.length + 1))) port closed
      (fun v => processed v ∨ v = port mate.length ∨ v = port (mate.length + 1)) := by
  intro v hv
  rcases hv with hv | rfl | rfl
  · rcases hc v hv with ⟨i, hi, hiv⟩ | ⟨c, hmem, hcv⟩
    · exact Or.inl ⟨i, (appendCup_live mate i).mpr (Or.inl hi), hiv.mono le_sup_left⟩
    · exact Or.inr ⟨c, hmem, hcv.mono le_sup_left⟩
  · exact Or.inl ⟨mate.length, (appendCup_live mate _).mpr (Or.inr (Or.inl rfl)),
      Reachable.refl _⟩
  · exact Or.inl ⟨mate.length + 1, (appendCup_live mate _).mpr (Or.inr (Or.inr rfl)),
      Reachable.refl _⟩

end Meanders.FirstCrossing
