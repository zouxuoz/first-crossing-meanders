import Meanders.Models.FirstCrossing.Native.Transition
import Meanders.Core.Graph.SupEdge

/-!
# Exact named-mate splice preservation

Consumed slots remain in the temporary array as `none`. The live relation
states bounds and involution directly through successful array lookups, without
assuming that the checked output of the transition is valid.
-/

namespace Meanders.FirstCrossing

/-- Joining named incidences does not edit any port group. -/
theorem spliceJoin_ports {w out : Splice} {x y : Nat}
    (h : spliceJoin w x y = some out) : out.ports = w.ports := by
  unfold spliceJoin at h
  split at h
  · simp at h
  · cases hx : (w.mate[x]?).join with
    | none => simp [hx] at h
    | some a =>
      cases hy : (w.mate[y]?).join with
      | none => simp [hx, hy] at h
      | some b =>
        simp only [hx, hy, Option.bind_eq_bind, Option.bind_some] at h
        split at h
        · simp at h
        · split at h
          · split at h
            · cases h; rfl
            · simp at h
          · split at h
            · simp at h
            · cases h; rfl


/-- A live named incidence has the specified live mate. -/
def HasMate (mate : List (Option ℕ)) (i j : ℕ) : Prop := mate[i]? = some (some j)

/-- An incidence is present in the current frontier. -/
def Live (mate : List (Option ℕ)) (i : ℕ) : Prop := ∃ j, HasMate mate i j

/-- Every live incidence has a distinct mate pointing back to it. Both indices
are in range because both lookups must return `some (some _)`. -/
def MateInvariant (mate : List (Option ℕ)) : Prop :=
  ∀ i j, HasMate mate i j → i ≠ j ∧ HasMate mate j i

/-- Array lookup is functional on named mates. -/
theorem HasMate.unique {mate : List (Option ℕ)} {i j k : ℕ}
    (hj : HasMate mate i j) (hk : HasMate mate i k) : j = k := by
  unfold HasMate at *
  rw [hj] at hk
  simpa using hk

/-- Successful mate lookup implies that its source index is in range. -/
theorem HasMate.bound {mate : List (Option ℕ)} {i j : ℕ}
    (h : HasMate mate i j) : i < mate.length := by
  by_contra hi
  have hn : mate[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
  rw [HasMate, hn] at h
  contradiction

/-- Live mate lookup is symmetric under the input invariant. -/
theorem MateInvariant.symm {mate : List (Option ℕ)} (hm : MateInvariant mate)
    {i j : ℕ} (h : HasMate mate i j) : HasMate mate j i := (hm i j h).2

/-- Looking into a known endpoint determines the unique other endpoint. -/
theorem MateInvariant.into_iff {mate : List (Option ℕ)} (hm : MateInvariant mate)
    {x a i : ℕ} (hx : HasMate mate x a) : HasMate mate i x ↔ i = a := by
  constructor
  · intro h
    exact (hx.unique (hm.symm h)).symm
  · rintro rfl
    exact hm.symm hx

/-- Looking out of a known endpoint determines its unique mate. -/
theorem HasMate.out_iff {mate : List (Option ℕ)} {x a i : ℕ}
    (hx : HasMate mate x a) : HasMate mate x i ↔ i = a := by
  constructor
  · intro h
    exact (hx.unique h).symm
  · rintro rfl
    exact hx

/-- Temporary array with the two joined incidences consumed. -/
def eraseJoined (mate : List (Option ℕ)) (x y : ℕ) : List (Option ℕ) :=
  (mate.set x none).set y none

/-- Temporary array when two distinct paths are joined at their consumed ends. -/
def rewireJoined (mate : List (Option ℕ)) (x y a b : ℕ) : List (Option ℕ) :=
  ((eraseJoined mate x y).set a (some b)).set b (some a)

/-- Exact lookup formula for consuming the two joined slots. -/
theorem eraseJoined_lookup {mate : List (Option ℕ)} {x y : ℕ}
    (hx : x < mate.length) (hy : y < mate.length) (i : ℕ) :
    (eraseJoined mate x y)[i]? =
      if y = i then some none else if x = i then some none else mate[i]? := by
  unfold eraseJoined
  rw [List.getElem?_set_of_lt' _ _ (by simpa using hy),
    List.getElem?_set_of_lt' _ _ hx]

/-- Consumed slots have no mate, and every other slot is unchanged. -/
theorem eraseJoined_hasMate {mate : List (Option ℕ)} {x y i j : ℕ}
    (hx : x < mate.length) (hy : y < mate.length) :
    HasMate (eraseJoined mate x y) i j ↔ i ≠ x ∧ i ≠ y ∧ HasMate mate i j := by
  unfold HasMate
  rw [eraseJoined_lookup hx hy]
  by_cases hxi : x = i <;> by_cases hyi : y = i <;> simp_all [eq_comm]

/-- Exact lookup formula in the nonclosing branch, with all writes in range. -/
theorem rewireJoined_lookup {mate : List (Option ℕ)} {x y a b : ℕ}
    (hx : x < mate.length) (hy : y < mate.length)
    (ha : a < mate.length) (hb : b < mate.length) (i : ℕ) :
    (rewireJoined mate x y a b)[i]? =
      if b = i then some (some a) else if a = i then some (some b)
      else if y = i then some none else if x = i then some none else mate[i]? := by
  unfold rewireJoined
  rw [List.getElem?_set_of_lt' _ _ (by simpa [eraseJoined] using hb),
    List.getElem?_set_of_lt' _ _ (by simpa [eraseJoined] using ha),
    eraseJoined_lookup hx hy]

/-- The nonclosing branch replaces exactly the pair of surviving path endpoints. -/
theorem rewireJoined_hasMate {mate : List (Option ℕ)} {x y a b i j : ℕ}
    (hx : x < mate.length) (hy : y < mate.length)
    (ha : a < mate.length) (hb : b < mate.length) (hab : a ≠ b) :
    HasMate (rewireJoined mate x y a b) i j ↔
      (i = a ∧ j = b) ∨ (i = b ∧ j = a) ∨
      (i ≠ x ∧ i ≠ y ∧ i ≠ a ∧ i ≠ b ∧ HasMate mate i j) := by
  unfold HasMate
  rw [rewireJoined_lookup hx hy ha hb]
  by_cases hbi : b = i <;> by_cases hai : a = i <;>
    by_cases hyi : y = i <;> by_cases hxi : x = i <;> simp_all [eq_comm]

/-- Distinct joined paths have four distinct named endpoints. -/
theorem MateInvariant.splice_distinct {mate : List (Option ℕ)} (hm : MateInvariant mate)
    {x y a b : ℕ} (hx : HasMate mate x a) (hy : HasMate mate y b)
    (hxy : x ≠ y) (hay : a ≠ y) :
    a ≠ x ∧ a ≠ y ∧ b ≠ x ∧ b ≠ y ∧ a ≠ b := by
  have hax := Ne.symm (hm x a hx).1
  have hby := Ne.symm (hm y b hy).1
  have hbx : b ≠ x := by
    intro he
    subst b
    exact hay (hx.unique (hm.symm hy))
  have hab : a ≠ b := by
    intro he
    subst b
    exact hxy ((hm.symm hx).unique (hm.symm hy))
  exact ⟨hax, hay, hbx, hby, hab⟩

/-- The executable closing branch is exactly two `none` writes and one cycle. -/
theorem spliceJoin_eq_close {w : Splice} {x y : ℕ}
    (hxy : x ≠ y) (hx : HasMate w.mate x y) (hy : HasMate w.mate y x) :
    spliceJoin w x y = some { w with
      mate := eraseJoined w.mate x y, cycles := w.cycles + 1 } := by
  simp [spliceJoin, HasMate] at hx hy ⊢
  simp [hx, hy, hxy, eraseJoined]

/-- The executable nonclosing branch performs exactly the four specified writes. -/
theorem spliceJoin_eq_rewire {w : Splice} {x y a b : ℕ}
    (hm : MateInvariant w.mate) (hx : HasMate w.mate x a) (hy : HasMate w.mate y b)
    (hxy : x ≠ y) (hay : a ≠ y) :
    spliceJoin w x y = some { w with mate := rewireJoined w.mate x y a b } := by
  obtain ⟨hax, -, hbx, hby, hab⟩ := hm.splice_distinct hx hy hxy hay
  have ha := hm.symm hx
  have hb := hm.symm hy
  simp only [HasMate] at hx hy ha hb
  simp [spliceJoin, hx, hy, ha, hb, hxy, hay, hbx, hab, rewireJoined, eraseJoined]

/-- The physical splice does not depend on the orientation of its two live ends. -/
theorem spliceJoin_comm {w : Splice} (hm : MateInvariant w.mate)
    {x y a b : ℕ} (hx : HasMate w.mate x a) (hy : HasMate w.mate y b)
    (hxy : x ≠ y) : spliceJoin w x y = spliceJoin w y x := by
  by_cases hay : a = y
  · subst a
    have hyx := hm.symm hx
    rw [spliceJoin_eq_close hxy hx hyx, spliceJoin_eq_close (Ne.symm hxy) hyx hx]
    have he : eraseJoined w.mate x y = eraseJoined w.mate y x := by
      apply List.ext_getElem?
      intro i
      rw [eraseJoined_lookup hx.bound hy.bound, eraseJoined_lookup hy.bound hx.bound]
      by_cases hxi : x = i <;> by_cases hyi : y = i <;> simp_all
    rw [he]
  · have hd := hm.splice_distinct hx hy hxy hay
    rw [spliceJoin_eq_rewire hm hx hy hxy hay,
      spliceJoin_eq_rewire hm hy hx (Ne.symm hxy) hd.2.2.1]
    have he : rewireJoined w.mate x y a b = rewireJoined w.mate y x b a := by
      apply List.ext_getElem?
      intro i
      rw [rewireJoined_lookup hx.bound hy.bound (hm.symm hx).bound (hm.symm hy).bound,
        rewireJoined_lookup hy.bound hx.bound (hm.symm hy).bound (hm.symm hx).bound]
      by_cases hai : a = i <;> by_cases hbi : b = i <;>
        by_cases hxi : x = i <;> by_cases hyi : y = i <;> simp_all
    rw [he]

/-- Closing one represented path consumes its two endpoints without disturbing others. -/
theorem eraseJoined_invariant {mate : List (Option ℕ)} (hm : MateInvariant mate)
    {x y : ℕ} (hx : HasMate mate x y) : MateInvariant (eraseJoined mate x y) := by
  have hy := hm.symm hx
  intro i j hij
  obtain ⟨hix, hiy, hij⟩ := (eraseJoined_hasMate hx.bound hy.bound).mp hij
  have hjx : j ≠ x := by
    intro he
    subst j
    exact hiy ((hm.into_iff hx).mp hij)
  have hjy : j ≠ y := by
    intro he
    subst j
    exact hix ((hm.into_iff hy).mp hij)
  exact ⟨(hm i j hij).1, (eraseJoined_hasMate hx.bound hy.bound).mpr
    ⟨hjx, hjy, hm.symm hij⟩⟩

/-- Splicing distinct represented paths preserves the live mate involution. -/
theorem rewireJoined_invariant {mate : List (Option ℕ)} (hm : MateInvariant mate)
    {x y a b : ℕ} (hx : HasMate mate x a) (hy : HasMate mate y b)
    (hxy : x ≠ y) (hay : a ≠ y) : MateInvariant (rewireJoined mate x y a b) := by
  obtain ⟨hax, hay, hbx, hby, hab⟩ := hm.splice_distinct hx hy hxy hay
  have ha := hm.symm hx
  have hb := hm.symm hy
  have hr := @rewireJoined_hasMate mate x y a b
  intro i j hij
  rcases (hr hx.bound hy.bound ha.bound hb.bound hab).mp hij with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hix, hiy, hia, hib, hij⟩
  · exact ⟨hab, (hr hx.bound hy.bound ha.bound hb.bound hab).mpr
      (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  · exact ⟨Ne.symm hab, (hr hx.bound hy.bound ha.bound hb.bound hab).mpr
      (Or.inl ⟨rfl, rfl⟩)⟩
  · have hjx : j ≠ x := by
      intro he
      subst j
      exact hia ((hm.into_iff hx).mp hij)
    have hjy : j ≠ y := by
      intro he
      subst j
      exact hib ((hm.into_iff hy).mp hij)
    have hja : j ≠ a := by
      intro he
      subst j
      exact hix ((hm.into_iff ha).mp hij)
    have hjb : j ≠ b := by
      intro he
      subst j
      exact hiy ((hm.into_iff hb).mp hij)
    exact ⟨(hm i j hij).1, (hr hx.bound hy.bound ha.bound hb.bound hab).mpr
      (Or.inr (Or.inr ⟨hjx, hjy, hja, hjb, hm.symm hij⟩))⟩

/-- Exactly the two joined names leave the live set in the closing branch. -/
theorem eraseJoined_live {mate : List (Option ℕ)} {x y i : ℕ}
    (hx : x < mate.length) (hy : y < mate.length) :
    Live (eraseJoined mate x y) i ↔ Live mate i ∧ i ≠ x ∧ i ≠ y := by
  simp only [Live, eraseJoined_hasMate hx hy]
  aesop

/-- Exactly the two joined names leave the live set in the splicing branch. -/
theorem rewireJoined_live {mate : List (Option ℕ)} (hm : MateInvariant mate)
    {x y a b i : ℕ} (hx : HasMate mate x a) (hy : HasMate mate y b)
    (hxy : x ≠ y) (hay : a ≠ y) :
    Live (rewireJoined mate x y a b) i ↔ Live mate i ∧ i ≠ x ∧ i ≠ y := by
  obtain ⟨hax, hay, hbx, hby, hab⟩ := hm.splice_distinct hx hy hxy hay
  have ha := hm.symm hx
  have hb := hm.symm hy
  have hr := @rewireJoined_hasMate mate x y a b
  constructor
  · rintro ⟨j, hij⟩
    rcases (hr hx.bound hy.bound ha.bound hb.bound hab).mp hij with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hix, hiy, -, -, hij⟩
    · exact ⟨⟨x, ha⟩, hax, hay⟩
    · exact ⟨⟨y, hb⟩, hbx, hby⟩
    · exact ⟨⟨j, hij⟩, hix, hiy⟩
  · rintro ⟨⟨j, hij⟩, hix, hiy⟩
    by_cases hia : i = a
    · subst i
      exact ⟨b, (hr hx.bound hy.bound ha.bound hb.bound hab).mpr
        (Or.inl ⟨rfl, rfl⟩)⟩
    by_cases hib : i = b
    · subst i
      exact ⟨a, (hr hx.bound hy.bound ha.bound hb.bound hab).mpr
        (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    exact ⟨j, (hr hx.bound hy.bound ha.bound hb.bound hab).mpr
      (Or.inr (Or.inr ⟨hix, hiy, hia, hib, hij⟩))⟩

/-- A valid physical join succeeds, preserves the actual array involution,
consumes exactly two names, and increments cycles exactly in the closing case. -/
theorem spliceJoin_spec {w : Splice} (hm : MateInvariant w.mate)
    {x y a b : ℕ} (hx : HasMate w.mate x a) (hy : HasMate w.mate y b) (hxy : x ≠ y) :
    ∃ out, spliceJoin w x y = some out ∧ MateInvariant out.mate ∧
      (∀ i, Live out.mate i ↔ Live w.mate i ∧ i ≠ x ∧ i ≠ y) ∧
      out.cycles = w.cycles + (if a = y then 1 else 0) ∧
      out.mate.length = w.mate.length ∧ out.ports = w.ports := by
  by_cases hay : a = y
  · subst a
    have hyx := hm.symm hx
    refine ⟨_, spliceJoin_eq_close hxy hx hyx, eraseJoined_invariant hm hx,
      fun i => eraseJoined_live hx.bound hy.bound, ?_, ?_, rfl⟩
    · simp
    · simp [eraseJoined]
  · refine ⟨_, spliceJoin_eq_rewire hm hx hy hxy hay,
      rewireJoined_invariant hm hx hy hxy hay,
      fun i => rewireJoined_live hm hx hy hxy hay, ?_, ?_, rfl⟩
    · simp [hay]
    · simp [rewireJoined, eraseJoined]

/-- Facts about a given successful executable result, without an output-validity assumption. -/
theorem spliceJoin_result {w out : Splice} (hm : MateInvariant w.mate)
    {x y a b : ℕ} (hx : HasMate w.mate x a) (hy : HasMate w.mate y b) (hxy : x ≠ y)
    (h : spliceJoin w x y = some out) :
    MateInvariant out.mate ∧
      (∀ i, Live out.mate i ↔ Live w.mate i ∧ i ≠ x ∧ i ≠ y) ∧
      out.cycles = w.cycles + (if a = y then 1 else 0) ∧
      out.mate.length = w.mate.length ∧ out.ports = w.ports := by
  obtain ⟨z, hz, hinv, hlive, hc, hlen, hp⟩ := spliceJoin_spec hm hx hy hxy
  have he : z = out := Option.some.inj (hz.symm.trans h)
  subst z
  exact ⟨hinv, hlive, hc, hlen, hp⟩

/-- Live mates encode exactly the paths between physical frontier incidences.
This relation deliberately says nothing about components without live endpoints. -/
def RepresentsLivePaths {V : Type*} (mate : List (Option ℕ)) (G : SimpleGraph V)
    (port : ℕ → V) : Prop :=
  ∀ i j, Live mate i → Live mate j →
    (G.Reachable (port i) (port j) ↔ i = j ∨ HasMate mate i j)

/-- Closing a represented path cannot change connectivity of surviving endpoints. -/
theorem eraseJoined_represents {V : Type*} {mate : List (Option ℕ)}
    {G : SimpleGraph V} {port : ℕ → V} (hm : MateInvariant mate)
    (hp : RepresentsLivePaths mate G port) {x y : ℕ} (hx : HasMate mate x y) :
    RepresentsLivePaths (eraseJoined mate x y)
      (G ⊔ SimpleGraph.edge (port x) (port y)) port := by
  have hy := hm.symm hx
  intro i j hi hj
  obtain ⟨hi, hix, hiy⟩ := (eraseJoined_live hx.bound hy.bound).mp hi
  obtain ⟨hj, hjx, hjy⟩ := (eraseJoined_live hx.bound hy.bound).mp hj
  rw [Meanders.reachable_sup_edge_iff, hp i j hi hj, hp i x hi ⟨y, hx⟩,
    hp y j ⟨x, hy⟩ hj, hp i y hi ⟨x, hy⟩, hp x j ⟨y, hx⟩ hj,
    hm.into_iff hx, hm.into_iff hy, eraseJoined_hasMate hx.bound hy.bound]
  simp [hix, hiy]

/-- Adding the physical joining edge gives exactly the rewritten mate paths. -/
theorem rewireJoined_represents {V : Type*} {mate : List (Option ℕ)}
    {G : SimpleGraph V} {port : ℕ → V} (hm : MateInvariant mate)
    (hp : RepresentsLivePaths mate G port) {x y a b : ℕ}
    (hx : HasMate mate x a) (hy : HasMate mate y b) (hxy : x ≠ y) (hay : a ≠ y) :
    RepresentsLivePaths (rewireJoined mate x y a b)
      (G ⊔ SimpleGraph.edge (port x) (port y)) port := by
  obtain ⟨hax, hay, hbx, hby, hab⟩ := hm.splice_distinct hx hy hxy hay
  have ha := hm.symm hx
  have hb := hm.symm hy
  intro i j hi hj
  obtain ⟨hi, hix, hiy⟩ := (rewireJoined_live hm hx hy hxy hay).mp hi
  obtain ⟨hj, hjx, hjy⟩ := (rewireJoined_live hm hx hy hxy hay).mp hj
  rw [Meanders.reachable_sup_edge_iff, hp i j hi hj, hp i x hi ⟨a, hx⟩,
    hp y j ⟨b, hy⟩ hj, hp i y hi ⟨b, hy⟩, hp x j ⟨a, hx⟩ hj,
    hm.into_iff hx, hm.into_iff hy, hy.out_iff, hx.out_iff,
    rewireJoined_hasMate hx.bound hy.bound ha.bound hb.bound hab]
  by_cases hia : i = a
  · subst i
    simp_all [ha.out_iff, eq_comm]
  by_cases hib : i = b
  · subst i
    simp_all [hb.out_iff, eq_comm]
  simp [hix, hiy, hia, hib, eq_comm]

/-- The actual successful executable splice represents the physical added edge.
No validity predicate on the checked output is assumed. -/
theorem spliceJoin_represents {V : Type*} {w out : Splice}
    {G : SimpleGraph V} {port : ℕ → V} (hm : MateInvariant w.mate)
    (hp : RepresentsLivePaths w.mate G port) {x y a b : ℕ}
    (hx : HasMate w.mate x a) (hy : HasMate w.mate y b) (hxy : x ≠ y)
    (h : spliceJoin w x y = some out) :
    RepresentsLivePaths out.mate (G ⊔ SimpleGraph.edge (port x) (port y)) port := by
  by_cases hay : a = y
  · subst a
    rw [spliceJoin_eq_close hxy hx (hm.symm hx)] at h
    cases h
    exact eraseJoined_represents hm hp hx
  · rw [spliceJoin_eq_rewire hm hx hy hxy hay] at h
    cases h
    exact rewireJoined_represents hm hp hx hy hxy hay

/-- A cycle is recorded exactly when the joined physical incidences were already
connected before adding their new edge. -/
theorem spliceJoin_cycle_iff_reachable {V : Type*} {w out : Splice}
    {G : SimpleGraph V} {port : ℕ → V} (hm : MateInvariant w.mate)
    (hp : RepresentsLivePaths w.mate G port) {x y a b : ℕ}
    (hx : HasMate w.mate x a) (hy : HasMate w.mate y b) (hxy : x ≠ y)
    (h : spliceJoin w x y = some out) :
    out.cycles = w.cycles + 1 ↔ G.Reachable (port x) (port y) := by
  obtain ⟨z, hz, -, -, hc, -, -⟩ := spliceJoin_spec hm hx hy hxy
  have he : z = out := Option.some.inj (hz.symm.trans h)
  subst z
  rw [hc, hp x y ⟨a, hx⟩ ⟨b, hy⟩, hx.out_iff]
  by_cases hay : a = y <;> simp_all [eq_comm]

end Meanders.FirstCrossing
