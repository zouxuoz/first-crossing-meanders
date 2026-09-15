import Meanders.Core.Overlay

/-!
# Coloured physical incidence graph

Each physical crossing has one upper and one lower incidence. The crossing
edge joins those incidences; matching edges join incidences of the same owner.
Thus coincident upper and lower arches remain different edges, including at
rank one. Collapsing crossing edges recovers the existing overlay connectivity.
-/

namespace Meanders.FirstCrossing

open SimpleGraph

/-- `true` is the upper matching and `false` the lower matching. -/
def ownerMatching {n : Nat} (p : NoncrossingMatching n × NoncrossingMatching n)
    (owner : Bool) : NoncrossingMatching n := if owner then p.1 else p.2

/-- Physical incidences, with a distinct vertex for each owner at every crossing. -/
abbrev Incidence (n : Nat) := Bool × Point n

/-- Crossing edges switch owner; matching edges preserve owner. -/
def incidenceGraph {n : Nat} (p : NoncrossingMatching n × NoncrossingMatching n) :
    SimpleGraph (Incidence n) where
  Adj u v := (u.2 = v.2 ∧ u.1 ≠ v.1) ∨
    (u.1 = v.1 ∧ (ownerMatching p u.1).partner u.2 = v.2)
  symm := ⟨by
    intro u v h
    rcases h with ⟨hp, ho⟩ | ⟨ho, hp⟩
    · exact Or.inl ⟨hp.symm, ho.symm⟩
    · refine Or.inr ⟨ho.symm, ?_⟩
      rw [← ho, ← hp, NoncrossingMatching.partner_partner]⟩
  loopless := ⟨by
    intro u h
    rcases h with ⟨_, ho⟩ | ⟨_, hp⟩
    · exact ho rfl
    · exact (ownerMatching p u.1).partner_ne u.2 hp⟩

instance {n : Nat} (p : NoncrossingMatching n × NoncrossingMatching n) :
    DecidableRel (incidenceGraph p).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem incidenceGraph_crossing {n : Nat}
    (p : NoncrossingMatching n × NoncrossingMatching n) (owner : Bool) (v : Point n) :
    (incidenceGraph p).Adj (owner, v) (!owner, v) := by
  left
  exact ⟨rfl, by cases owner <;> simp⟩

theorem incidenceGraph_matching {n : Nat}
    (p : NoncrossingMatching n × NoncrossingMatching n) (owner : Bool) (v : Point n) :
    (incidenceGraph p).Adj (owner, v) (owner, (ownerMatching p owner).partner v) :=
  Or.inr ⟨rfl, rfl⟩

/-- Every incidence has exactly the crossing neighbour and its same-owner mate.
The two neighbours remain distinct even when upper and lower arches coincide. -/
theorem incidenceGraph_adj_iff {n : Nat}
    (p : NoncrossingMatching n × NoncrossingMatching n) (u v : Incidence n) :
    (incidenceGraph p).Adj u v ↔
      v = (!u.1, u.2) ∨ v = (u.1, (ownerMatching p u.1).partner u.2) := by
  rcases u with ⟨a, u⟩
  rcases v with ⟨b, v⟩
  cases a <;> cases b <;> simp [incidenceGraph, eq_comm]

theorem incidenceGraph_degree {n : Nat}
    (p : NoncrossingMatching n × NoncrossingMatching n) (u : Incidence n) :
    (incidenceGraph p).degree u = 2 := by
  have hn : (incidenceGraph p).neighborFinset u =
      {(!u.1, u.2), (u.1, (ownerMatching p u.1).partner u.2)} := by
    ext v
    simp only [mem_neighborFinset, incidenceGraph_adj_iff, Finset.mem_insert,
      Finset.mem_singleton]
  rw [degree, hn]
  have hne : (!u.1, u.2) ≠ (u.1, (ownerMatching p u.1).partner u.2) := by
    intro he
    have ho := congrArg Prod.fst he
    cases u.1 <;> simp at ho
  simp [hne]

/-- Projection of one physical edge either collapses a crossing edge or follows
one of the original two coloured matching edges. -/
theorem incidenceGraph_adj_project {n : Nat}
    (p : NoncrossingMatching n × NoncrossingMatching n) {u v : Incidence n}
    (h : (incidenceGraph p).Adj u v) :
    u.2 = v.2 ∨ (unionGraph p).Adj u.2 v.2 := by
  rcases h with ⟨hp, _⟩ | ⟨_, hp⟩
  · exact Or.inl hp
  · right
    rw [unionGraph_adj]
    refine ⟨?_, ?_⟩
    · intro he
      rw [← he] at hp
      exact (ownerMatching p u.1).partner_ne u.2 hp
    · cases ho : u.1
      · exact Or.inr (by simpa [ownerMatching, ho] using hp)
      · exact Or.inl (by simpa [ownerMatching, ho] using hp)

theorem incidenceGraph_reachable_project {n : Nat}
    (p : NoncrossingMatching n × NoncrossingMatching n) {u v : Incidence n}
    (h : (incidenceGraph p).Reachable u v) :
    (unionGraph p).Reachable u.2 v.2 := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Reachable.refl _
  | tail _ hadj ih =>
    rcases incidenceGraph_adj_project p hadj with he | he
    · exact he ▸ ih
    · exact ih.trans he.reachable

/-- The two owners over a physical point belong to the same component. -/
theorem incidenceGraph_switch_reachable {n : Nat}
    (p : NoncrossingMatching n × NoncrossingMatching n) (a b : Bool) (v : Point n) :
    (incidenceGraph p).Reachable (a, v) (b, v) := by
  cases a <;> cases b
  · exact Reachable.refl _
  · exact (incidenceGraph_crossing p false v).reachable
  · exact (incidenceGraph_crossing p true v).reachable
  · exact Reachable.refl _

/-- Every overlay edge lifts through its actual matching owner; the owners at
the two ends of the lifted path can be chosen independently. -/
theorem incidenceGraph_lift_edge {n : Nat}
    (p : NoncrossingMatching n × NoncrossingMatching n) {u v : Point n}
    (h : (unionGraph p).Adj u v) (a b : Bool) :
    (incidenceGraph p).Reachable (a, u) (b, v) := by
  rcases (unionGraph_adj p u v).mp h with ⟨_, h | h⟩
  · have hm := (incidenceGraph_matching p true u).reachable
    simp only [ownerMatching, ↓reduceIte, h] at hm
    exact (incidenceGraph_switch_reachable p a true u).trans
      (hm.trans (incidenceGraph_switch_reachable p true b v))
  · have hm := (incidenceGraph_matching p false u).reachable
    simp only [ownerMatching, Bool.false_eq_true, ↓reduceIte, h] at hm
    exact (incidenceGraph_switch_reachable p a false u).trans
      (hm.trans (incidenceGraph_switch_reachable p false b v))

theorem incidenceGraph_reachable_lift {n : Nat}
    (p : NoncrossingMatching n × NoncrossingMatching n) {u v : Point n}
    (h : (unionGraph p).Reachable u v) (a b : Bool) :
    (incidenceGraph p).Reachable (a, u) (b, v) := by
  have hf : (incidenceGraph p).Reachable (false, u) (false, v) := by
    rw [reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Reachable.refl _
    | tail _ hadj ih => exact ih.trans (incidenceGraph_lift_edge p hadj false false)
  exact (incidenceGraph_switch_reachable p a false u).trans
    (hf.trans (incidenceGraph_switch_reachable p false b v))

/-- The incidence graph and the public overlay have precisely the same
components after projecting to physical crossings. -/
theorem incidenceGraph_reachable_iff {n : Nat}
    (p : NoncrossingMatching n × NoncrossingMatching n) (u v : Incidence n) :
    (incidenceGraph p).Reachable u v ↔ (unionGraph p).Reachable u.2 v.2 :=
  ⟨incidenceGraph_reachable_project p,
    fun h => incidenceGraph_reachable_lift p h u.1 v.1⟩

/-- Connectivity uses the existing public convention at rank zero as well. -/
theorem incidenceGraph_connected_iff {n : Nat}
    (p : NoncrossingMatching n × NoncrossingMatching n) :
    (incidenceGraph p).Connected ↔ (unionGraph p).Connected := by
  constructor
  · intro h
    obtain ⟨⟨_, v⟩⟩ := h.nonempty
    let : Nonempty (Point n) := ⟨v⟩
    refine ⟨fun u v => ?_⟩
    exact incidenceGraph_reachable_project p (h.preconnected (false, u) (false, v))
  · intro h
    obtain ⟨v⟩ := h.nonempty
    let : Nonempty (Incidence n) := ⟨(false, v)⟩
    refine ⟨fun u v => ?_⟩
    exact (incidenceGraph_reachable_iff p u v).mpr (h.preconnected u.2 v.2)

end Meanders.FirstCrossing
