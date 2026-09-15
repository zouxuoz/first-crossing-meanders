import Meanders.Models.FirstCrossing.Surgery.Splice
import Meanders.Models.FirstCrossing.Native.Codec

/-!
# Native cup creation and owner attachment

The candidate's two appended array entries are a new independent incidence
path. The proofs below interpret those exact writes and the executable owner
attachment, including its removal of the newest physical group endpoint.
-/

namespace Meanders.FirstCrossing

open SimpleGraph

/-- Appending the two fresh incidences changes exactly their two mate entries. -/
theorem appendCup_hasMate (mate : List (Option Nat)) (i j : Nat) :
    HasMate (mate ++ [some (mate.length + 1), some mate.length]) i j ↔
      HasMate mate i j ∨ (i = mate.length ∧ j = mate.length + 1) ∨
        (i = mate.length + 1 ∧ j = mate.length) := by
  unfold HasMate
  by_cases hi : i < mate.length
  · rw [List.getElem?_append_left hi]
    simp only [show i ≠ mate.length by omega, show i ≠ mate.length + 1 by omega,
      false_and, or_false]
  · have hold : mate[i]? = none := List.getElem?_eq_none (by omega)
    rw [List.getElem?_append_right (by omega), hold]
    by_cases h0 : i = mate.length
    · subst i
      simp [eq_comm]
    · by_cases h1 : i = mate.length + 1
      · subst i
        simp [eq_comm]
      · have hd : 2 ≤ i - mate.length := by omega
        have hsuf : [some (mate.length + 1), some mate.length][i - mate.length]? = none :=
          List.getElem?_eq_none (by simpa using hd)
        rw [hsuf]
        simp [h0, h1]

/-- Cup creation makes exactly its two new names live. -/
theorem appendCup_live (mate : List (Option Nat)) (i : Nat) :
    Live (mate ++ [some (mate.length + 1), some mate.length]) i ↔
      Live mate i ∨ i = mate.length ∨ i = mate.length + 1 := by
  simp only [Live, appendCup_hasMate]
  aesop

/-- The actual appended pair preserves the live mate involution. -/
theorem appendCup_invariant {mate : List (Option Nat)} (hm : MateInvariant mate) :
    MateInvariant (mate ++ [some (mate.length + 1), some mate.length]) := by
  intro i j hij
  rcases (appendCup_hasMate mate i j).mp hij with hij | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨(hm i j hij).1, (appendCup_hasMate mate j i).mpr (Or.inl (hm.symm hij))⟩
  · exact ⟨by omega, (appendCup_hasMate mate _ _).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
  · exact ⟨by omega, (appendCup_hasMate mate _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩

/-- Embedding the raw mate list introduces no absent live slots. -/
theorem mapSome_hasMate (mate : List Nat) (i j : Nat) :
    HasMate (mate.map some) i j ↔ mate[i]? = some j := by
  simp only [HasMate, List.getElem?_map]
  cases h : mate[i]? <;> simp

/-- The checked raw key is already a live involution before adding the cup. -/
theorem pairingValid_mateInvariant {mate : List Nat} (h : pairingValid mate = true) :
    MateInvariant (mate.map some) := by
  intro i j hij
  have hij' := (mapSome_hasMate mate i j).mp hij
  have hi : i < mate.length := by simpa only [List.length_map] using hij.bound
  obtain ⟨k, hik, hne, hki⟩ := (pairingValid_iff mate).mp h i hi
  have he : j = k := Option.some.inj (hij'.symm.trans hik)
  subst k
  exact ⟨hne, (mapSome_hasMate mate j i).mpr hki⟩

/-- Adding the actual candidate cup edge extends the represented paths by one
independent two-incidence path. Injectivity is required only on this finite array. -/
theorem appendCup_represents {V : Type*} {mate : List (Option Nat)} {G : SimpleGraph V}
    {port : Nat → V} (hm : MateInvariant mate) (hp : RepresentsLivePaths mate G port)
    (hinj : Set.InjOn port (Set.Iio (mate.length + 2)))
    (h0 : ∀ v, G.Reachable (port mate.length) v ↔ v = port mate.length)
    (h1 : ∀ v, G.Reachable (port (mate.length + 1)) v ↔ v = port (mate.length + 1)) :
    RepresentsLivePaths (mate ++ [some (mate.length + 1), some mate.length])
      (G ⊔ edge (port mate.length) (port (mate.length + 1))) port := by
  intro i j hi hj
  have hib : i < mate.length + 2 := by
    obtain ⟨k, hk⟩ := hi
    simpa only [List.length_append, List.length_cons, List.length_nil] using hk.bound
  have hjb : j < mate.length + 2 := by
    obtain ⟨k, hk⟩ := hj
    simpa only [List.length_append, List.length_cons, List.length_nil] using hk.bound
  have heq {a b : Nat} (ha : a < mate.length + 2) (hb : b < mate.length + 2) :
      port a = port b ↔ a = b := ⟨hinj ha hb, congrArg port⟩
  have hout0 (k : Nat) : ¬ HasMate mate mate.length k := by
    intro hk
    have := hk.bound
    omega
  have hout1 (k : Nat) : ¬ HasMate mate (mate.length + 1) k := by
    intro hk
    have := hk.bound
    omega
  have hin0 (k : Nat) : ¬ HasMate mate k mate.length := fun hk => hout0 k (hm.symm hk)
  have hin1 (k : Nat) : ¬ HasMate mate k (mate.length + 1) := fun hk => hout1 k (hm.symm hk)
  have hbase : G.Reachable (port i) (port j) ↔ i = j ∨ HasMate mate i j := by
    by_cases hi0 : i = mate.length
    · subst i
      rw [h0, heq hjb (by omega)]
      simp only [hout0, or_false, eq_comm]
    by_cases hi1 : i = mate.length + 1
    · subst i
      rw [h1, heq hjb (by omega)]
      simp only [hout1, or_false, eq_comm]
    by_cases hj0 : j = mate.length
    · subst j
      rw [reachable_comm, h0, heq hib (by omega)]
      simp only [hin0, or_false]
    by_cases hj1 : j = mate.length + 1
    · subst j
      rw [reachable_comm, h1, heq hib (by omega)]
      simp only [hin1, or_false]
    have hiold := ((appendCup_live mate i).mp hi).resolve_right
      (fun he => he.elim hi0 hi1)
    have hjold := ((appendCup_live mate j).mp hj).resolve_right
      (fun he => he.elim hj0 hj1)
    exact hp i j hiold hjold
  rw [reachable_sup_edge_isolated h0 h1, hbase, heq hib (by omega),
    heq hjb (by omega), heq hib (by omega), heq hjb (by omega), appendCup_hasMate]
  simp only [or_assoc]

/-- The exact candidate array represents the new physical crossing edge. -/
theorem candidateCup_represents {V : Type*} {mate : List Nat} {G : SimpleGraph V}
    {port : Nat → V} (h : pairingValid mate = true)
    (hp : RepresentsLivePaths (mate.map some) G port)
    (hinj : Set.InjOn port (Set.Iio (mate.length + 2)))
    (h0 : ∀ v, G.Reachable (port mate.length) v ↔ v = port mate.length)
    (h1 : ∀ v, G.Reachable (port (mate.length + 1)) v ↔ v = port (mate.length + 1)) :
    RepresentsLivePaths (mate.map some ++ [some (mate.length + 1), some mate.length])
      (G ⊔ edge (port mate.length) (port (mate.length + 1))) port := by
  simpa only [List.length_map] using
    appendCup_represents (pairingValid_mateInvariant h) hp
      (by simpa only [List.length_map] using hinj)
      (by simpa only [List.length_map] using h0)
      (by simpa only [List.length_map] using h1)

/-- An opening owner step appends its new incidence as the newest group endpoint. -/
theorem attachOwner_up_eq (w : Splice) (g : Group) (cup : Nat) :
    attachOwner w g false cup =
      some {w with ports := w.ports.set g (w.ports.get g ++ [cup])} := rfl

/-- Opening changes only group membership; the already-added cup path is unchanged. -/
theorem attachOwner_up_result {V : Type*} {w out : Splice} {g : Group} {cup : Nat}
    {G : SimpleGraph V} {port : Nat → V}
    (hm : MateInvariant w.mate) (hp : RepresentsLivePaths w.mate G port)
    (h : attachOwner w g false cup = some out) :
    out.ports.get g = w.ports.get g ++ [cup] ∧ out.mate = w.mate ∧
      out.cycles = w.cycles ∧ MateInvariant out.mate ∧ RepresentsLivePaths out.mate G port := by
  rw [attachOwner_up_eq] at h
  cases h
  refine ⟨?_, rfl, rfl, hm, hp⟩
  cases g <;> rfl

/-- A down step joins the actual newest endpoint of the indicated owner group. -/
theorem attachOwner_down_eq (w : Splice) (g : Group) (cup old : Nat) (older : List Nat)
    (htop : w.ports.get g = older ++ [old]) :
    attachOwner w g true cup = spliceJoin {w with ports := w.ports.set g older} old cup := by
  simp only [attachOwner, ite_true, htop, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.reverse_reverse]

/-- A legitimate newest-endpoint down attachment succeeds with the exact array
splice and physical owner edge, even when that edge closes an existing path. -/
theorem attachOwner_down_spec {V : Type*} {w : Splice} {g : Group}
    {cup old a b : Nat} {older : List Nat} {G : SimpleGraph V} {port : Nat → V}
    (htop : w.ports.get g = older ++ [old]) (hm : MateInvariant w.mate)
    (hp : RepresentsLivePaths w.mate G port) (hold : HasMate w.mate old a)
    (hcup : HasMate w.mate cup b) (hne : old ≠ cup) :
    ∃ out, attachOwner w g true cup = some out ∧ MateInvariant out.mate ∧
      RepresentsLivePaths out.mate (G ⊔ edge (port old) (port cup)) port ∧
      (∀ i, Live out.mate i ↔ Live w.mate i ∧ i ≠ old ∧ i ≠ cup) ∧
      out.cycles = w.cycles + (if a = cup then 1 else 0) ∧
      out.mate.length = w.mate.length ∧ out.ports = w.ports.set g older := by
  let start : Splice := {w with ports := w.ports.set g older}
  obtain ⟨out, hout, hinv, hlive, hc, hlen, hports⟩ :=
    spliceJoin_spec (w := start) hm hold hcup hne
  refine ⟨out, ?_, hinv, ?_, hlive, hc, hlen, hports⟩
  · rw [attachOwner_down_eq w g cup old older htop]
    exact hout
  · exact spliceJoin_represents (w := start) hm hp hold hcup hne hout

/-- The successful native down result carries the same exact physical interpretation. -/
theorem attachOwner_down_result {V : Type*} {w out : Splice} {g : Group}
    {cup old a b : Nat} {older : List Nat} {G : SimpleGraph V} {port : Nat → V}
    (htop : w.ports.get g = older ++ [old]) (hm : MateInvariant w.mate)
    (hp : RepresentsLivePaths w.mate G port) (hold : HasMate w.mate old a)
    (hcup : HasMate w.mate cup b) (hne : old ≠ cup)
    (h : attachOwner w g true cup = some out) :
    MateInvariant out.mate ∧
      RepresentsLivePaths out.mate (G ⊔ edge (port old) (port cup)) port ∧
      (∀ i, Live out.mate i ↔ Live w.mate i ∧ i ≠ old ∧ i ≠ cup) ∧
      out.cycles = w.cycles + (if a = cup then 1 else 0) ∧
      out.mate.length = w.mate.length ∧ out.ports = w.ports.set g older := by
  obtain ⟨z, hz, hinv, hpz, hlive, hc, hlen, hports⟩ :=
    attachOwner_down_spec htop hm hp hold hcup hne
  have he : z = out := Option.some.inj (hz.symm.trans h)
  subst z
  exact ⟨hinv, hpz, hlive, hc, hlen, hports⟩

end Meanders.FirstCrossing
