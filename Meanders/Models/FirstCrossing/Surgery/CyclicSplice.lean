import Meanders.Models.FirstCrossing.Surgery.Normalize
import Meanders.Models.FirstCrossing.Native.State
import Meanders.Models.FirstCrossing.Original.Pairing
import Mathlib.Data.List.Rotate

/-!
# Native cyclic splice preservation

Temporary arrays can contain consumed holes. A distinct list enumerating all
live names transports the actual checker to its canonical noncrossing matching.
Adjacent cap surgery is then compared with the exact native array writes.
-/

namespace Meanders.FirstCrossing

/-- The physical name at a geometric cyclic boundary position. -/
def cyclicName {n : Nat} (names : List Nat) (hlen : names.length = 2 * n)
    (i : Point n) : Nat := names[i.val]'(by omega)

/-- Exact named-array interpretation of a cyclic noncrossing matching. -/
def RepresentsCyclic {n : Nat} (mate : List (Option Nat)) (names : List Nat)
    (hlen : names.length = 2 * n) (m : NoncrossingMatching n) : Prop :=
  ∀ i j, HasMate mate (cyclicName names hlen i) (cyclicName names hlen j) ↔ m.partner i = j

/-- Relabelling actual successful mate lookups commutes with the native checker. -/
theorem cyclicCheck_named_conjugate {size : Nat} (mate : List (Option Nat)) (raw : List Nat)
    (f : Fin size → Fin size) (name : Fin size → Nat) (hinj : Function.Injective name)
    (hraw : ∀ i, raw[i.val]? = some (f i).val)
    (hname : ∀ i, HasMate mate (name i) (name (f i)))
    (xs stack : List (Fin size)) :
    cyclicCheck mate (xs.map name) (stack.map name) =
      cyclicCheck (raw.map some) (xs.map Fin.val) (stack.map Fin.val) := by
  have hm (i : Fin size) : mate[name i]?.join = some (name (f i)) := by
    rw [show mate[name i]? = some (some (name (f i))) from hname i]
    rfl
  have hr (i : Fin size) : (raw.map some)[i.val]?.join = some (f i).val := by
    rw [List.getElem?_map, hraw i]
    rfl
  induction xs generalizing stack with
  | nil => cases stack <;> rfl
  | cons x xs ih =>
      cases stack with
      | nil =>
          simp only [List.map_cons, List.map_nil, cyclicCheck, hm, hr]
          exact ih [f x]
      | cons y ys =>
          by_cases he : x = y
          · subst y
            simp only [List.map_cons, cyclicCheck, beq_self_eq_true, ite_true]
            exact ih ys
          · have hnn : name x ≠ name y := fun h => he (hinj h)
            have hii : x.val ≠ y.val := fun h => he (Fin.ext h)
            have hn : (name x == name y) = false := by simp [hnn]
            have hi : (x.val == y.val) = false := by simp [hii]
            simp only [List.map_cons, cyclicCheck, hn, hi, Bool.false_eq_true, ite_false, hm, hr]
            exact ih (f x :: y :: ys)

/-- Distinct listed names give an injective geometric boundary map. -/
theorem cyclicName_injective {n : Nat} (names : List Nat) (hlen : names.length = 2 * n)
    (hn : names.Nodup) : Function.Injective (cyclicName names hlen) := by
  intro i j he
  have hf : (⟨i.val, by omega⟩ : Fin names.length) = ⟨j.val, by omega⟩ := hn.get_inj_iff.mp he
  exact Fin.ext (congrArg (fun z : Fin names.length => z.val) hf)

/-- Enumerating geometric positions returns the exact supplied names. -/
theorem cyclicName_finRange {n : Nat} (names : List Nat) (hlen : names.length = 2 * n) :
    (List.finRange (2 * n)).map (cyclicName names hlen) = names := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 2 * n
  · have hib : i < names.length := by omega
    simp [cyclicName, hi, hib]
  · rw [List.getElem?_eq_none (by simp only [List.length_map, List.length_finRange]; omega),
      List.getElem?_eq_none (by omega)]

/-- A geometric named matching is accepted by the actual temporary-array checker. -/
theorem cyclicCheck_of_represents {n : Nat} {mate : List (Option Nat)} {names : List Nat}
    {hlen : names.length = 2 * n} {m : NoncrossingMatching n} (hn : names.Nodup)
    (hr : RepresentsCyclic mate names hlen m) : cyclicCheck mate names [] = true := by
  let raw := encodeMatching m (Equiv.refl (Point n))
  have hl (i : Point n) : raw[i.val]? = some (m.partner i).val := by
    exact getElem?_encodeMatching m (Equiv.refl _) i.isLt
  have hh := cyclicCheck_named_conjugate mate raw m.partner (cyclicName names hlen)
    (cyclicName_injective names hlen hn) hl (fun i => (hr i (m.partner i)).mpr rfl)
    (List.finRange (2 * n)) []
  rw [cyclicName_finRange] at hh
  simp only [List.map_nil] at hh
  have hfin : (List.finRange (2 * n)).map Fin.val = List.range (2 * n) := by simp
  rw [hfin] at hh
  apply hh.trans
  apply cyclicCheck_of_matching m raw
  intro i hi
  rw [m.partnerIndex_eq hi]
  exact hl ⟨i, hi⟩

/-- Any exact live-name enumeration can be used as a normalization view.
This changes no mate entry and invokes the existing normalization implementation. -/
def cyclicView (mate : List (Option Nat)) (names : List Nat) : Splice :=
  ⟨⟨[], names, [], []⟩, mate, 0⟩

@[simp] theorem cyclicView_flat (mate : List (Option Nat)) (names : List Nat) :
    (cyclicView mate names).ports.flat = names := by simp [cyclicView, Ports.flat]

/-- Accepted named arrays have an actual noncrossing matching interpretation.
Distinctness and exact live coverage are required explicitly, including consumed holes. -/
theorem exists_representsCyclic {mate : List (Option Nat)} {names : List Nat}
    (hn : names.Nodup) (hm : MateInvariant mate)
    (hc : ∀ x, x ∈ names ↔ Live mate x) (hcheck : cyclicCheck mate names [] = true) :
    ∃ (n : Nat) (hlen : names.length = 2 * n) (m : NoncrossingMatching n),
      RepresentsCyclic mate names hlen m := by
  let w := cyclicView mate names
  have hflat : w.ports.flat = names := cyclicView_flat mate names
  have hnd : w.ports.flat.Nodup := by rw [hflat]; exact hn
  have hcov : CoversLive w := by
    intro x
    change x ∈ w.ports.flat ↔ Live mate x
    rw [hflat]
    exact hc x
  obtain ⟨out, hout⟩ := normalize_total hnd hm hcov Counters.zero
  have hvalid := normalize_pairingValid hout hnd hm hcov
  have hlenraw : out.mate.length = names.length := (normalize_length hout).trans
    (congrArg List.length hflat)
  obtain ⟨n, hnraw⟩ : ∃ n, out.mate.length = 2 * n := by
    obtain ⟨k, hk⟩ := pairingValid_even_length hvalid
    exact ⟨k, by omega⟩
  have hlen : names.length = 2 * n := hlenraw.symm.trans hnraw
  let order : Point n ≃ Fin out.mate.length := finCongr hnraw.symm
  let f := cyclicPartner out.mate hvalid order
  have hraw (i : Point n) : out.mate[i.val]? = some (f i).val := by
    have hi : i.val < out.mate.length := by have := i.isLt; omega
    change out.mate[i.val]? = some out.mate[i.val]
    exact List.getElem?_eq_getElem hi
  have hconj (i j : Point n) : out.mate[i.val]? = some j.val ↔
      HasMate mate (cyclicName names hlen i) (cyclicName names hlen j) := by
    apply normalize_conjugates hout hnd hm hcov
    · rw [hflat]
      exact List.getElem?_eq_getElem (by have := i.isLt; omega)
    · rw [hflat]
      exact List.getElem?_eq_getElem (by have := j.isLt; omega)
  have hname (i : Point n) : HasMate mate (cyclicName names hlen i)
      (cyclicName names hlen (f i)) := (hconj i (f i)).mp (hraw i)
  have htransport := cyclicCheck_named_conjugate mate out.mate f (cyclicName names hlen)
    (cyclicName_injective names hlen hn) hraw hname (List.finRange (2 * n)) []
  rw [cyclicName_finRange] at htransport
  simp only [List.map_nil] at htransport
  have hfin : (List.finRange (2 * n)).map Fin.val = List.range (2 * n) := by simp
  rw [hfin] at htransport
  have horder : cyclicOrder order = List.range (2 * n) := by simp [cyclicOrder, order]
  have hnc := cyclicCheck_noncrossing out.mate hvalid order (by
    rw [horder]
    exact htransport.symm.trans hcheck)
  refine ⟨n, hlen, matchingOfRaw out.mate hvalid order hnc, ?_⟩
  intro i j
  rw [← hconj i j, hraw i, Option.some.injEq, partner_matchingOfRaw]
  exact Fin.ext_iff.symm

/-- The pairing graph is used only to compare the existing geometric and raw
splice theorems; each of its nontrivial components is one represented path. -/
private def mateGraph (mate : List (Option Nat)) (hm : MateInvariant mate) : SimpleGraph Nat where
  Adj := HasMate mate
  symm := ⟨fun _ _ h => hm.symm h⟩
  loopless := ⟨fun i h => (hm i i h).1 rfl⟩

private theorem mateGraph_reachable (mate : List (Option Nat)) (hm : MateInvariant mate)
    (i j : Nat) : (mateGraph mate hm).Reachable i j ↔ i = j ∨ HasMate mate i j := by
  constructor
  · rintro ⟨walk⟩
    induction walk with
    | nil => exact Or.inl rfl
    | cons hstep walk ih =>
        rcases ih with rfl | htail
        · exact Or.inr hstep
        · exact Or.inl ((hm.symm hstep).unique htail)
  · rintro (rfl | h)
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable h

private theorem mateGraph_represents (mate : List (Option Nat)) (hm : MateInvariant mate) :
    RepresentsLivePaths mate (mateGraph mate hm) id := by
  intro i j _ _
  exact mateGraph_reachable mate hm i j

/-- A listed geometric name is a live endpoint, with its displayed matching partner. -/
theorem RepresentsCyclic.live {n : Nat} {mate : List (Option Nat)} {names : List Nat}
    {hlen : names.length = 2 * n} {m : NoncrossingMatching n}
    (hr : RepresentsCyclic mate names hlen m) (i : Point n) :
    Live mate (cyclicName names hlen i) := ⟨_, (hr i (m.partner i)).mpr rfl⟩

private theorem representsCyclic_paths {n : Nat} {mate : List (Option Nat)}
    {names : List Nat} {hlen : names.length = 2 * n} {m : NoncrossingMatching n}
    (hm : MateInvariant mate) (hn : names.Nodup) (hr : RepresentsCyclic mate names hlen m) :
    RepresentsPaths (mateGraph mate hm) (fun i => (names[i]?).getD 0) m := by
  intro i j hi hj
  let u : Point n := ⟨i, hi⟩
  let v : Point n := ⟨j, hj⟩
  have hi' : i < names.length := by omega
  have hj' : j < names.length := by omega
  have he (a : Nat) (ha : a < 2 * n) :
      (names[a]?).getD 0 = cyclicName names hlen ⟨a, ha⟩ := by
    simp only [List.getElem?_eq_getElem (show a < names.length by omega), Option.getD_some]
    rfl
  dsimp only
  rw [he i hi, he j hj, mateGraph_reachable, hr, m.partnerIndex_eq hi]
  have hname : cyclicName names hlen u = cyclicName names hlen v ↔ i = j :=
    ⟨fun heq => congrArg Fin.val ((cyclicName_injective names hlen hn) heq),
      fun heq => congrArg (cyclicName names hlen) (Fin.ext heq)⟩
  change (cyclicName names hlen u = cyclicName names hlen v ∨ m.partner u = v) ↔ _
  rw [hname, Fin.ext_iff]

/-- The native join at the front cyclic seam realizes the existing geometric cap.
The comparison uses the exact input pairing graph and both proved splice semantics. -/
theorem spliceJoin_representsCyclic_front {n : Nat} {w out : Splice}
    {x y : Nat} {rest : List Nat} {hlen : (x :: y :: rest).length = 2 * (n + 1)}
    {m : NoncrossingMatching (n + 1)} (hn : (x :: y :: rest).Nodup)
    (hm : MateInvariant w.mate) (hr : RepresentsCyclic w.mate (x :: y :: rest) hlen m)
    (hjoin : spliceJoin w x y = some out) :
    ∃ hrest : rest.length = 2 * n, RepresentsCyclic out.mate rest hrest (adjacentCap m).2 := by
  have hrest : rest.length = 2 * n := by simp only [List.length_cons] at hlen; omega
  have hnrest : rest.Nodup := hn.tail.tail
  have hxy : x ≠ y := fun he => (List.nodup_cons.mp hn).1 (by simp [he])
  let zero : Point (n + 1) := ⟨0, by omega⟩
  let one : Point (n + 1) := ⟨1, by omega⟩
  let a := cyclicName (x :: y :: rest) hlen (m.partner zero)
  let b := cyclicName (x :: y :: rest) hlen (m.partner one)
  have hx : HasMate w.mate x a := (hr zero (m.partner zero)).mpr rfl
  have hy : HasMate w.mate y b := (hr one (m.partner one)).mpr rfl
  have hout := spliceJoin_result hm hx hy hxy hjoin
  have hraw := spliceJoin_represents hm (mateGraph_represents w.mate hm) hx hy hxy hjoin
  have hgeo := adjacentCap_representsPaths (representsCyclic_paths hm hn hr)
  let port : Nat → Nat := fun i => ((x :: y :: rest)[i]?).getD 0
  change RepresentsPaths (mateGraph w.mate hm ⊔ SimpleGraph.edge x y)
    (fun i => port (i + 2)) (adjacentCap m).2 at hgeo
  have hname (i : Point n) : port (i.val + 2) = cyclicName rest hrest i := by
    simp only [port, List.getElem?_cons_succ, List.getElem?_eq_getElem
      (show i.val < rest.length by have := i.isLt; omega), Option.getD_some]
    rfl
  have hlive (i : Point n) : Live out.mate (cyclicName rest hrest i) := by
    have hi : i.val + 2 < 2 * (n + 1) := by have := i.isLt; omega
    have hold : Live w.mate (cyclicName rest hrest i) := hr.live ⟨i.val + 2, hi⟩
    have him : cyclicName rest hrest i ∈ rest := List.getElem_mem _
    have hix : cyclicName rest hrest i ≠ x := by
      intro he
      rw [he] at him
      exact (List.nodup_cons.mp hn).1 (List.mem_cons_of_mem _ him)
    have hiy : cyclicName rest hrest i ≠ y := by
      intro he
      rw [he] at him
      exact (List.nodup_cons.mp hn.tail).1 him
    exact (hout.2.1 _).mpr ⟨hold, hix, hiy⟩
  refine ⟨hrest, ?_⟩
  intro i j
  have hp := hraw (cyclicName rest hrest i) (cyclicName rest hrest j) (hlive i) (hlive j)
  dsimp only [id_eq] at hp
  have hg := hgeo i.val j.val i.isLt j.isLt
  dsimp only at hg
  rw [hname i, hname j] at hg
  have heNames : cyclicName rest hrest i = cyclicName rest hrest j ↔ i = j :=
    ⟨fun he => cyclicName_injective rest hrest hnrest he, congrArg (cyclicName rest hrest)⟩
  have hePartner : (adjacentCap m).2.partnerIndex i.val = j.val ↔
      (adjacentCap m).2.partner i = j := by
    rw [NoncrossingMatching.partnerIndex_eq _ i.isLt]
    exact Fin.ext_iff.symm
  have he := hp.symm.trans hg
  rw [heNames, ← Fin.ext_iff, hePartner] at he
  by_cases hij : i = j
  · subst j
    constructor
    · intro hmself
      exact ((hout.1 _ _ hmself).1 rfl).elim
    · intro hpSelf
      exact ((adjacentCap m).2.partner_ne i hpSelf).elim
  · simpa only [hij, false_or] using he

/-- The actual native join preserves the checker when its ports lead the cyclic list. -/
theorem spliceJoin_cyclicCheck_front {w out : Splice} {x y : Nat} {rest : List Nat}
    (hn : (x :: y :: rest).Nodup) (hm : MateInvariant w.mate)
    (hc : ∀ i, i ∈ x :: y :: rest ↔ Live w.mate i)
    (hcheck : cyclicCheck w.mate (x :: y :: rest) [] = true)
    (hjoin : spliceJoin w x y = some out) : cyclicCheck out.mate rest [] = true := by
  obtain ⟨n, hlen, m, hr⟩ := exists_representsCyclic hn hm hc hcheck
  cases n with
  | zero => simp at hlen
  | succ n =>
      obtain ⟨hrest, hout⟩ := spliceJoin_representsCyclic_front hn hm hr hjoin
      exact cyclicCheck_of_represents hn.tail.tail hout

/-- One forward cyclic step on positions in an even port boundary. -/
def rotatePosition {n : Nat} (i : Point n) : Point n :=
  ⟨nextPort (2 * n) i.val, nextPort_lt i.isLt⟩

/-- The one-step position map remains injective, including the empty boundary. -/
theorem rotatePosition_injective {n : Nat} : Function.Injective (@rotatePosition n) := by
  intro i j hij
  exact Fin.ext (nextPort_injective _ (congrArg Fin.val hij))

/-- Physical matching rotation commutes with the explicit forward position map. -/
theorem rotatePosition_partner {n : Nat} (m : NoncrossingMatching n) (i : Point n) :
    rotatePosition ((NoncrossingMatching.rotate m).partner i) =
      m.partner (rotatePosition i) := by
  apply Fin.ext
  change nextPort (2 * n) ((NoncrossingMatching.rotate m).partner i).val =
    (m.partner (rotatePosition i)).val
  rw [← NoncrossingMatching.partnerIndex_eq _ i.isLt,
    nextPort_partnerIndex_rotate m i.isLt,
    NoncrossingMatching.partnerIndex_eq _ (nextPort_lt i.isLt)]
  rfl

/-- Rotating a named list once pulls back its names along the same position map. -/
theorem getElem_rotate_one_next {n : Nat} (names : List Nat)
    (hlen : names.length = 2 * n) (i : Point n) :
    (names.rotate 1)[i.val]'(by simpa only [List.length_rotate, hlen] using i.isLt) =
      names[(rotatePosition i).val]'(by simpa only [hlen] using (rotatePosition i).isLt) := by
  rw [List.getElem_rotate]
  congr 1
  change (i.val + 1) % names.length = nextPort (2 * n) i.val
  rw [hlen]
  by_cases h : i.val + 1 = 2 * n
  · simp [nextPort, h]
  · have hi : i.val + 1 < 2 * n := by omega
    simp [nextPort, h, Nat.mod_eq_of_lt hi]

/-- A named mate representation rotates without changing any mate entries. -/
theorem namedMatching_rotate_one {n : Nat} {mate : List (Option Nat)}
    {names : List Nat} (hlen : names.length = 2 * n) {m : NoncrossingMatching n}
    (hrep : ∀ i j : Point n,
      HasMate mate (names[i.val]'(by simpa only [hlen] using i.isLt))
        (names[j.val]'(by simpa only [hlen] using j.isLt)) ↔ m.partner i = j) :
    ∀ i j : Point n,
      HasMate mate
        ((names.rotate 1)[i.val]'(by simpa only [List.length_rotate, hlen] using i.isLt))
        ((names.rotate 1)[j.val]'(by simpa only [List.length_rotate, hlen] using j.isLt)) ↔
      (NoncrossingMatching.rotate m).partner i = j := by
  intro i j
  rw [getElem_rotate_one_next names hlen i, getElem_rotate_one_next names hlen j,
    hrep, ← rotatePosition_partner]
  exact rotatePosition_injective.eq_iff

/-- The shared named noncrossing representation is invariant under one rotation. -/
theorem RepresentsCyclic.rotate_one {n : Nat} {mate : List (Option Nat)}
    {names : List Nat} {hlen : names.length = 2 * n} {m : NoncrossingMatching n}
    (hrep : RepresentsCyclic mate names hlen m) :
    RepresentsCyclic mate (names.rotate 1) (by simpa using hlen)
      (NoncrossingMatching.rotate m) :=
  namedMatching_rotate_one hlen hrep

/-- Repeated rotation preserves the exact named pairing interpretation. -/
theorem RepresentsCyclic.rotate {n : Nat} {mate : List (Option Nat)}
    {names : List Nat} {hlen : names.length = 2 * n} {m : NoncrossingMatching n}
    (hrep : RepresentsCyclic mate names hlen m) (k : Nat) :
    RepresentsCyclic mate (names.rotate k) (by simpa using hlen)
      ((NoncrossingMatching.rotate)^[k] m) := by
  induction k with
  | zero => simpa using hrep
  | succ k ih =>
    have hnext := ih.rotate_one
    simpa only [List.rotate_rotate, Function.iterate_succ_apply'] using hnext

/-- Moving an initial block to the end preserves the same mate array. -/
theorem RepresentsCyclic.swap_blocks {n : Nat} {mate : List (Option Nat)}
    {before after : List Nat} {hlen : (before ++ after).length = 2 * n}
    {m : NoncrossingMatching n} (hrep : RepresentsCyclic mate (before ++ after) hlen m) :
    RepresentsCyclic mate (after ++ before) (by simpa [Nat.add_comm] using hlen)
      ((NoncrossingMatching.rotate)^[before.length] m) := by
  have h := hrep.rotate before.length
  simpa only [List.rotate_append_length_eq] using h

/-- The actual named checker accepts every rotation of an exact live frontier. -/
theorem cyclicCheck_rotate {mate : List (Option Nat)} {names : List Nat}
    (hn : names.Nodup) (hm : MateInvariant mate)
    (hc : ∀ x, x ∈ names ↔ Live mate x) (hcheck : cyclicCheck mate names [] = true)
    (k : Nat) : cyclicCheck mate (names.rotate k) [] = true := by
  obtain ⟨n, hlen, m, hr⟩ := exists_representsCyclic hn hm hc hcheck
  exact cyclicCheck_of_represents (List.nodup_rotate.mpr hn) (hr.rotate k)

/-- Changing the start seam of the exact live cyclic order changes no acceptance. -/
theorem cyclicCheck_swap_blocks_iff {mate : List (Option Nat)}
    {before after : List Nat} (hn : (before ++ after).Nodup)
    (hm : MateInvariant mate) (hc : ∀ x, x ∈ before ++ after ↔ Live mate x) :
    cyclicCheck mate (before ++ after) [] = true ↔
      cyclicCheck mate (after ++ before) [] = true := by
  constructor
  · intro hcheck
    simpa only [List.rotate_append_length_eq] using
      cyclicCheck_rotate hn hm hc hcheck before.length
  · intro hcheck
    have hn' : (after ++ before).Nodup := by
      simpa only [List.rotate_append_length_eq] using
        (List.nodup_rotate.mpr hn : ((before ++ after).rotate before.length).Nodup)
    have hc' : ∀ x, x ∈ after ++ before ↔ Live mate x := by
      intro x
      simpa only [List.mem_append, or_comm] using hc x
    simpa only [List.rotate_append_length_eq] using
      cyclicCheck_rotate hn' hm hc' hcheck after.length

/-- An interior consecutive pair can be brought to the working cap seam and
rotated back after the exact native join. -/
theorem spliceJoin_cyclicCheck_blocks {w out : Splice} {x y : Nat}
    {before after : List Nat} (hn : (before ++ [x, y] ++ after).Nodup)
    (hm : MateInvariant w.mate)
    (hc : ∀ i, i ∈ before ++ [x, y] ++ after ↔ Live w.mate i)
    (hcheck : cyclicCheck w.mate (before ++ [x, y] ++ after) [] = true)
    (hjoin : spliceJoin w x y = some out) :
    cyclicCheck out.mate (before ++ after) [] = true := by
  have hn' : (before ++ ([x, y] ++ after)).Nodup := by
    simpa only [List.append_assoc] using hn
  have hc' : ∀ i, i ∈ before ++ ([x, y] ++ after) ↔ Live w.mate i := by
    simpa only [List.append_assoc] using hc
  have hcheck' : cyclicCheck w.mate (before ++ ([x, y] ++ after)) [] = true := by
    simpa only [List.append_assoc] using hcheck
  have hnfront : (x :: y :: (after ++ before)).Nodup := by
    simpa only [List.cons_append, List.nil_append, List.append_assoc] using
      (List.perm_append_comm.nodup_iff.mp hn')
  have hcfront : ∀ i, i ∈ x :: y :: (after ++ before) ↔ Live w.mate i := by
    intro i
    simpa [List.mem_append, or_assoc, or_comm, or_left_comm] using hc i
  have hfront : cyclicCheck w.mate (x :: y :: (after ++ before)) [] = true := by
    simpa only [List.cons_append, List.nil_append, List.append_assoc] using
      (cyclicCheck_swap_blocks_iff hn' hm hc').mp hcheck'
  have hcap := spliceJoin_cyclicCheck_front hnfront hm hcfront hfront hjoin
  obtain ⟨a, hx⟩ := (hcfront x).mp (by simp)
  obtain ⟨b, hy⟩ := (hcfront y).mp (by simp)
  have hxy : x ≠ y := fun he => (List.nodup_cons.mp hnfront).1 (by simp [he])
  have hout := spliceJoin_result hm hx hy hxy hjoin
  have hcov : ∀ i, i ∈ after ++ before ↔ Live out.mate i := by
    intro i
    have hnx : x ∉ after ++ before :=
      fun h => (List.nodup_cons.mp hnfront).1 (List.mem_cons_of_mem _ h)
    have hny : y ∉ after ++ before := (List.nodup_cons.mp hnfront.tail).1
    constructor
    · intro hi
      exact (hout.2.1 i).mpr ⟨(hcfront i).mp (by simp only [List.mem_cons]; tauto),
        fun he => hnx (he ▸ hi), fun he => hny (he ▸ hi)⟩
    · intro hi
      obtain ⟨hold, hix, hiy⟩ := (hout.2.1 i).mp hi
      have hmem := (hcfront i).mpr hold
      simp only [List.mem_cons] at hmem
      exact (hmem.resolve_left hix).resolve_left hiy
  exact (cyclicCheck_swap_blocks_iff hnfront.tail.tail hout.1 hcov).mp hcap

/-- The wrap seam joins the last endpoint to the first without changing owners. -/
theorem spliceJoin_cyclicCheck_wrap {w out : Splice} {x y : Nat} {middle : List Nat}
    (hn : ([y] ++ middle ++ [x]).Nodup) (hm : MateInvariant w.mate)
    (hc : ∀ i, i ∈ [y] ++ middle ++ [x] ↔ Live w.mate i)
    (hcheck : cyclicCheck w.mate ([y] ++ middle ++ [x]) [] = true)
    (hjoin : spliceJoin w x y = some out) : cyclicCheck out.mate middle [] = true := by
  have hnfront : (x :: y :: middle).Nodup := by
    simpa only [List.cons_append, List.nil_append] using
      (List.perm_append_comm.nodup_iff.mp hn)
  have hcfront : ∀ i, i ∈ x :: y :: middle ↔ Live w.mate i := by
    intro i
    simpa [List.mem_append, or_assoc, or_comm, or_left_comm] using hc i
  have hfront : cyclicCheck w.mate (x :: y :: middle) [] = true := by
    simpa only [List.cons_append, List.nil_append] using
      (cyclicCheck_swap_blocks_iff hn hm hc).mp hcheck
  exact spliceJoin_cyclicCheck_front hnfront hm hcfront hfront hjoin

private theorem filter_remove_eq_self {names : List Nat} {x y : Nat}
    (hx : x ∉ names) (hy : y ∉ names) :
    names.filter (fun i => i != x && i != y) = names := by
  apply List.filter_eq_self.mpr
  intro i hi
  have hix : i ≠ x := fun he => hx (he ▸ hi)
  have hiy : i ≠ y := fun he => hy (he ▸ hi)
  simp [hix, hiy]

/-- Removing an interior adjacent pair retains exactly the surrounding order. -/
theorem filter_remove_blocks {before after : List Nat} {x y : Nat}
    (hn : (before ++ [x, y] ++ after).Nodup) :
    (before ++ [x, y] ++ after).filter (fun i => i != x && i != y) = before ++ after := by
  have hn' : (before ++ (x :: y :: after)).Nodup := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hn
  obtain ⟨-, hna, hd⟩ := List.nodup_append.mp hn'
  have hxb : x ∉ before := fun hx => hd x hx x (by simp) rfl
  have hyb : y ∉ before := fun hy => hd y hy y (by simp) rfl
  have hxa : x ∉ after := fun hx => (List.nodup_cons.mp hna).1 (by simp [hx])
  have hya : y ∉ after := (List.nodup_cons.mp hna.tail).1
  simp only [List.filter_append, filter_remove_eq_self hxb hyb,
    filter_remove_eq_self hxa hya]
  simp

/-- Removing a wrapping adjacent pair retains exactly the middle order. -/
theorem filter_remove_wrap {middle : List Nat} {x y : Nat}
    (hn : ([y] ++ middle ++ [x]).Nodup) :
    ([y] ++ middle ++ [x]).filter (fun i => i != x && i != y) = middle := by
  obtain ⟨hnm, -, hd⟩ := List.nodup_append.mp hn
  have hxm : x ∉ middle := fun hx => hd x (by simp [hx]) x (by simp) rfl
  have hym : y ∉ middle := (List.nodup_cons.mp hnm).1
  simp only [List.filter_append, filter_remove_eq_self hxm hym]
  simp

/-- Both ports named by an actual cyclic seam occur in its endpoint enumeration. -/
theorem AtSeam.members {names : List Nat} {x y : Nat} (h : AtSeam names x y) :
    x ∈ names ∧ y ∈ names := by
  rcases h with ⟨before, after, rfl⟩ | ⟨middle, rfl⟩ <;> simp

/-- The actual native join preserves planarity at an oriented cyclic seam,
including wrap-around. Output order deletes exactly the consumed two names. -/
theorem spliceJoin_cyclicCheck_seam {w out : Splice} {names : List Nat} {x y : Nat}
    (hn : names.Nodup) (hm : MateInvariant w.mate)
    (hc : ∀ i, i ∈ names ↔ Live w.mate i) (hcheck : cyclicCheck w.mate names [] = true)
    (hseam : AtSeam names x y) (hjoin : spliceJoin w x y = some out) :
    cyclicCheck out.mate (names.filter (fun i => i != x && i != y)) [] = true := by
  rcases hseam with ⟨before, after, rfl⟩ | ⟨middle, rfl⟩
  · rw [filter_remove_blocks hn]
    exact spliceJoin_cyclicCheck_blocks hn hm hc hcheck hjoin
  · rw [filter_remove_wrap hn]
    exact spliceJoin_cyclicCheck_wrap hn hm hc hcheck hjoin

/-- Seam orientation never exchanges owners: reversing the join arguments is
justified by the proved symmetry of the exact native array writes. -/
theorem spliceJoin_cyclicCheck_adjacent {w out : Splice} {names : List Nat} {x y : Nat}
    (hn : names.Nodup) (hm : MateInvariant w.mate)
    (hc : ∀ i, i ∈ names ↔ Live w.mate i) (hcheck : cyclicCheck w.mate names [] = true)
    (hseam : AtSeam names x y ∨ AtSeam names y x)
    (hjoin : spliceJoin w x y = some out) :
    cyclicCheck out.mate (names.filter (fun i => i != x && i != y)) [] = true := by
  rcases hseam with hseam | hseam
  · exact spliceJoin_cyclicCheck_seam hn hm hc hcheck hseam hjoin
  · obtain ⟨hyMem, hxMem⟩ := hseam.members
    obtain ⟨a, hx⟩ := (hc x).mp hxMem
    obtain ⟨b, hy⟩ := (hc y).mp hyMem
    have hxy : x ≠ y := by
      intro he
      subst y
      simp [spliceJoin] at hjoin
    have hrev : spliceJoin w y x = some out := by
      rw [← spliceJoin_comm hm hx hy hxy]
      exact hjoin
    have hout := spliceJoin_cyclicCheck_seam hn hm hc hcheck hseam hrev
    simpa only [Bool.and_comm] using hout

end Meanders.FirstCrossing
