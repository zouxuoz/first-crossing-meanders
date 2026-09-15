import Meanders.Models.FirstCrossing.Interpretation.SourceRepresentation
import Meanders.Models.FirstCrossing.Surgery.VisitCoverage
import Meanders.Models.FirstCrossing.Surgery.CandidateFacts

/-!
# Source graphs and native surgery

These lemmas identify the physical graphs supplied to the native path
preservation theorems. Original through-edge predicates are equated with the
actual native FIFO head edges, without a successor-representation premise.
-/

namespace Meanders.FirstCrossing

open SimpleGraph

/-- The physical edges of one owner's newly shared through ordinal. -/
def Source.ownerThroughGraph {spec : RunSpec} (s : Source spec)
    (t : Stage) (side : Side) (owner : Bool) : SimpleGraph (Incidence spec.n) where
  Adj a b := a.1 = owner ∧ b.1 = owner ∧
    (ownerMatching s.matchings owner).partner a.2 = b.2 ∧
    s.throughAdded t side owner a.2 b.2
  symm := ⟨by
    intro a b ⟨ha, hb, hp, he⟩
    refine ⟨hb, ha, ?_, he.elim Or.inr Or.inl⟩
    rw [← hp, NoncrossingMatching.partner_partner]⟩
  loopless := ⟨by
    intro a ⟨_, _, hp, _⟩
    exact (ownerMatching s.matchings owner).partner_ne a.2 hp⟩

/-- No newly shared ordinal means no through edge for that owner. -/
theorem Source.ownerThroughGraph_eq_bot {spec : RunSpec} (s : Source spec)
    (t : Stage) (side : Side) (owner : Bool)
    (hzero : s.joined (t.next side) (Group.onSide owner .left) -
      s.joined t (Group.onSide owner .left) = 0) :
    s.ownerThroughGraph t side owner = ⊥ := by
  ext a b
  simp only [Source.ownerThroughGraph, bot_adj, iff_false]
  rintro ⟨_, _, _, he⟩
  simp only [Source.throughAdded] at he
  omega

/-- Enabled FIFO heads determine the entire newly added original owner graph. -/
theorem Source.ownerThroughGraph_eq_edge {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side))
    (owner : Bool) (a b : Point spec.n)
    (hleft : (s.beforeDrainGroup t side (Group.onSide owner .left)).head? = some (owner, a))
    (hright : (s.beforeDrainGroup t side (Group.onSide owner .right)).head? = some (owner, b))
    (hnew : s.joined t (Group.onSide owner .left) <
      s.joined (t.next side) (Group.onSide owner .left)) :
    s.ownerThroughGraph t side owner = edge (owner, a) (owner, b) := by
  obtain ⟨hp, he⟩ := s.drain_heads_source_edge hnext owner a b hleft hright hnew
  have hne : (owner, a) ≠ (owner, b) := by
    intro hh
    exact (ownerMatching s.matchings owner).partner_ne a
      (hp.trans (congrArg Prod.snd hh).symm)
  ext x y
  rw [edge_adj]
  constructor
  · rintro ⟨hx, hy, hxy, hadded⟩
    have hnxy : x ≠ y := by
      intro heq
      exact (ownerMatching s.matchings owner).partner_ne x.2
        (hxy.trans (congrArg Prod.snd heq).symm)
    refine ⟨?_, hnxy⟩
    rcases hadded with hforward | hreverse
    · have hheads := s.throughAdded_heads hnext owner x.2 y.2 hxy
        hforward.1 hforward.2.1 (Or.inl hforward)
      have hxa := congrArg Prod.snd (Option.some.inj (hheads.1.symm.trans hleft))
      have hyb := congrArg Prod.snd (Option.some.inj (hheads.2.symm.trans hright))
      exact Or.inl ⟨Prod.ext hx hxa, Prod.ext hy hyb⟩
    · have hyx : (ownerMatching s.matchings owner).partner y.2 = x.2 := by
        rw [← hxy, NoncrossingMatching.partner_partner]
      have hheads := s.throughAdded_heads hnext owner y.2 x.2 hyx
        hreverse.1 hreverse.2.1 (Or.inl hreverse)
      have hya := congrArg Prod.snd (Option.some.inj (hheads.1.symm.trans hleft))
      have hxb := congrArg Prod.snd (Option.some.inj (hheads.2.symm.trans hright))
      exact Or.inr ⟨Prod.ext hx hxb, Prod.ext hy hya⟩
  · rintro ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩
    · exact ⟨rfl, rfl, hp, he⟩
    · refine ⟨rfl, rfl, ?_, he.elim Or.inr Or.inl⟩
      rw [← hp, NoncrossingMatching.partner_partner]

/-- Post-attachment physical endpoint groups retain their original owner label. -/
theorem Source.beforeDrainGroup_owner {spec : RunSpec} (s : Source spec)
    (t : Stage) (side : Side) (g : Group) {a : Incidence spec.n}
    (ha : a ∈ s.beforeDrainGroup t side g) : a.1 = g.upper := by
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  rfl

/-- A native FIFO drain, whose two groups name the actual post-attachment lists,
adds exactly the original newly joined through-edge graph. -/
theorem Source.addFifoEdges_eq_ownerThrough {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side)) (owner : Bool)
    (G : SimpleGraph (Incidence spec.n)) (port : Nat → Incidence spec.n) (p : Ports)
    (hl : (p.get (Group.onSide owner .left)).map port =
      s.beforeDrainGroup t side (Group.onSide owner .left))
    (hr : (p.get (Group.onSide owner .right)).map port =
      s.beforeDrainGroup t side (Group.onSide owner .right)) :
    addFifoEdges G port (fifoEdges
      (s.joined (t.next side) (Group.onSide owner .left) -
        s.joined t (Group.onSide owner .left)) p
      (Group.onSide owner .left) (Group.onSide owner .right)) =
        G ⊔ s.ownerThroughGraph t side owner := by
  have hdelta := s.joined_next_between t side (Group.onSide owner .left)
  rcases (show s.joined (t.next side) (Group.onSide owner .left) -
      s.joined t (Group.onSide owner .left) = 0 ∨
      s.joined (t.next side) (Group.onSide owner .left) -
        s.joined t (Group.onSide owner .left) = 1 by omega) with hk | hk
  · rw [s.ownerThroughGraph_eq_bot t side owner hk, hk]
    simp [fifoEdges, addFifoEdges]
  · have hnew : s.joined t (Group.onSide owner .left) <
        s.joined (t.next side) (Group.onSide owner .left) := by omega
    have hneL := s.beforeDrainGroup_nonempty hnext (Group.onSide owner .left) hnew
    have hnewR : s.joined t (Group.onSide owner .right) <
        s.joined (t.next side) (Group.onSide owner .right) := by
      simpa only [s.joined_onSide_right] using hnew
    have hneR := s.beforeDrainGroup_nonempty hnext (Group.onSide owner .right) hnewR
    cases hpl : p.get (Group.onSide owner .left) with
    | nil => exact False.elim (hneL (hl.symm.trans (by simp [hpl])))
    | cons x xs =>
      cases hpr : p.get (Group.onSide owner .right) with
      | nil => exact False.elim (hneR (hr.symm.trans (by simp [hpr])))
      | cons y ys =>
        have hx : (s.beforeDrainGroup t side (Group.onSide owner .left)).head? = some (port x) := by
          rw [← hl, hpl]
          rfl
        have hy : (s.beforeDrainGroup t side (Group.onSide owner .right)).head? =
            some (port y) := by
          rw [← hr, hpr]
          rfl
        have hxo : (port x).1 = owner := by
          have hh := s.beforeDrainGroup_owner t side _ (List.mem_of_head? hx)
          cases owner <;> exact hh
        have hyo : (port y).1 = owner := by
          have hh := s.beforeDrainGroup_owner t side _ (List.mem_of_head? hy)
          cases owner <;> exact hh
        have hx' : port x = (owner, (port x).2) := Prod.ext hxo rfl
        have hy' : port y = (owner, (port y).2) := Prod.ext hyo rfl
        have hg := s.ownerThroughGraph_eq_edge hnext owner (port x).2 (port y).2
          (hx.trans (congrArg some hx')) (hy.trans (congrArg some hy')) hnew
        rw [hk, fifoEdges_one hpl hpr, hg]
        simp only [addFifoEdges, List.foldl_cons, List.foldl_nil]
        rw [← hx', ← hy']

private theorem owner_partner_edge_adj {n : Nat} (m : NoncrossingMatching n)
    (owner : Bool) (p : Point n) (a b : Incidence n) :
    (edge (owner, m.partner p) (owner, p)).Adj a b ↔
      a.1 = owner ∧ b.1 = owner ∧ m.partner a.2 = b.2 ∧ (a.2 = p ∨ b.2 = p) := by
  rw [edge_adj]
  constructor
  · rintro ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩
    · exact ⟨rfl, rfl, m.partner_partner p, Or.inr rfl⟩
    · exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
  · rintro ⟨ha, hb, hp, he⟩
    have hne : a ≠ b := by
      intro heq
      exact m.partner_ne a.2 (hp.trans (congrArg Prod.snd heq).symm)
    refine ⟨?_, hne⟩
    rcases he with he | he
    · have hb' : b.2 = m.partner p := by rw [← hp, he]
      exact Or.inr ⟨Prod.ext ha he, Prod.ext hb hb'⟩
    · have ha' : a.2 = m.partner p := by rw [← he, ← hp, m.partner_partner]
      exact Or.inl ⟨Prod.ext ha ha', Prod.ext hb he⟩

/-- The owner's physical attachment edge, selected by its actual source D bit. -/
def Source.ownerAttachmentGraph {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side))
    (owner : Bool) : SimpleGraph (Incidence spec.n) :=
  if (if owner then (s.nextMove t side).upperDown else (s.nextMove t side).lowerDown) then
    edge (owner, (ownerMatching s.matchings owner).partner (s.newPoint hnext))
      (owner, s.newPoint hnext)
  else ⊥

/-- The selected source owner edge is exactly the internal attachment event. -/
theorem Source.ownerAttachmentGraph_adj_iff {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (owner : Bool) (a b : Incidence spec.n) :
    (s.ownerAttachmentGraph hnext owner).Adj a b ↔
      a.1 = owner ∧ b.1 = owner ∧ (ownerMatching s.matchings owner).partner a.2 = b.2 ∧
        s.internalAdded t (s.newPoint hnext) a.2 b.2 := by
  have hcongr : (a.1 = owner ∧ b.1 = owner ∧
      (ownerMatching s.matchings owner).partner a.2 = b.2 ∧
        s.internalAdded t (s.newPoint hnext) a.2 b.2) ↔
      (a.1 = owner ∧ b.1 = owner ∧
      (ownerMatching s.matchings owner).partner a.2 = b.2 ∧
        ((if owner then (s.nextMove t side).upperDown else (s.nextMove t side).lowerDown) = true ∧
          (a.2 = s.newPoint hnext ∨ b.2 = s.newPoint hnext))) := by
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    apply and_congr_right
    intro hp
    exact s.internalAdded_matching_iff ht hnext owner a.2 b.2 hp
  rw [hcongr]
  unfold Source.ownerAttachmentGraph
  by_cases hd : (if owner then (s.nextMove t side).upperDown
    else (s.nextMove t side).lowerDown) = true
  · rw [ite_eq_left hd, owner_partner_edge_adj]
    simp only [hd, true_and]
  · rw [ite_eq_right hd]
    simp only [bot_adj, hd, Bool.false_eq_true, false_and, and_false]

/-- The graph added by a visit splits into the physical crossing, the two
original owner attachments, and the two independently prescribed FIFO drains. -/
theorem Source.visitEdges_decomposition {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side)) :
    s.visitEdges hnext =
      edge (true, s.newPoint hnext) (false, s.newPoint hnext) ⊔
      s.ownerAttachmentGraph hnext true ⊔ s.ownerAttachmentGraph hnext false ⊔
      s.ownerThroughGraph t side true ⊔ s.ownerThroughGraph t side false := by
  ext a b
  simp only [sup_adj, s.ownerAttachmentGraph_adj_iff ht hnext,
    Source.ownerThroughGraph, Source.visitEdges, edge_adj]
  rcases a with ⟨ao, a⟩
  rcases b with ⟨bo, b⟩
  cases ao <;> cases bo <;> simp only [Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false,
    false_and, true_and, and_false, false_or, or_false, not_false_eq_true,
    not_true_eq_false, and_true, ne_eq]
  all_goals aesop

/-- The original next partial graph is precisely the ordered physical graph
used by cup creation, upper/lower attachment, and upper/lower FIFO draining. -/
theorem Source.partialGraph_next_decomposition {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side)) :
    s.partialGraph (t.next side) =
      s.partialGraph t ⊔ edge (true, s.newPoint hnext) (false, s.newPoint hnext) ⊔
      s.ownerAttachmentGraph hnext true ⊔ s.ownerAttachmentGraph hnext false ⊔
      s.ownerThroughGraph t side true ⊔ s.ownerThroughGraph t side false := by
  rw [s.partialGraph_next ht hnext, s.visitEdges_decomposition ht hnext]
  simp only [sup_assoc]

/-- Matching all four concrete group lists matches the canonical physical storage order. -/
theorem Source.flat_map_eq_boundary {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (port : Nat → Incidence spec.n) (p : Ports)
    (hgroups : ∀ g, (p.get g).map port = s.retainedGroup ht g) :
    p.flat.map port = s.retainedBoundary ht := by
  simp only [Ports.flat, List.map_append, Source.retainedBoundary]
  exact congrArg₂ (· ++ ·)
    (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (hgroups .pl) (hgroups .pr)) (hgroups .ql))
    (hgroups .qr)

/-- Native normalization transports the derived raw live-path invariant and
exact physical group order to the canonical source/key representation. -/
theorem Source.normalize_representsKey {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) {w : Splice} {out : Key}
    (port : Nat → Incidence spec.n)
    (hn : w.ports.flat.Nodup) (hm : MateInvariant w.mate) (hc : CoversLive w)
    (hp : RepresentsLivePaths w.mate (s.partialGraph t) port)
    (hgroups : ∀ g, (w.ports.get g).map port = s.retainedGroup ht g)
    (h : normalize (s.counters t) w = some out) : s.RepresentsKey ht out := by
  have hmap := s.flat_map_eq_boundary ht port w.ports hgroups
  have hlength : w.ports.flat.length = (s.retainedBoundary ht).length := by
    simpa only [List.length_map] using congrArg List.length hmap
  have houtlength : out.mate.length = (s.retainedBoundary ht).length :=
    (normalize_length h).trans hlength
  refine ⟨normalize_counters h, houtlength, ?_⟩
  intro i j
  have hport (k : Fin (s.retainedBoundary ht).length) :
      normalizedPort w port k.val = (s.retainedBoundary ht)[k.val] := by
    have hk : k.val < w.ports.flat.length := by simpa only [hlength] using k.isLt
    have hlookup := List.getElem?_eq_getElem (l := w.ports.flat) hk
    have hnames : (w.ports.flat.map port)[k.val]? = some ((s.retainedBoundary ht)[k.val]) := by
      rw [hmap]
      exact List.getElem?_eq_getElem k.isLt
    rw [List.getElem?_map, hlookup, Option.map_some] at hnames
    rw [normalizedPort_eq hlookup, Option.some.inj hnames]
  have hpaths := normalize_paths h hn hm hc hp
    (by simpa only [houtlength] using i.isLt)
    (by simpa only [houtlength] using j.isLt)
  simpa only [hport, Fin.ext_iff] using hpaths

/-- The exact native newest-slot graph for a successful owner attachment is its
original physical source attachment graph. -/
theorem Source.attachment_graph_eq {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (owner : Bool) {w out : Splice} (cup : Nat) (port : Nat → Incidence spec.n)
    (G : SimpleGraph (Incidence spec.n))
    (hnames : (w.ports.get (Group.onSide owner side)).map port =
      s.retainedGroup ht (Group.onSide owner side))
    (hcup : port cup = (owner, s.newPoint hnext))
    (hattach : attachOwner w (Group.onSide owner side)
      (if owner then (s.nextMove t side).upperDown else (s.nextMove t side).lowerDown)
      cup = some out) :
    (if (if owner then (s.nextMove t side).upperDown else (s.nextMove t side).lowerDown) then
      G ⊔ edge (port ((w.ports.get (Group.onSide owner side)).getLast?.getD 0)) (port cup)
      else G) = G ⊔ s.ownerAttachmentGraph hnext owner := by
  let down := if owner then (s.nextMove t side).upperDown else (s.nextMove t side).lowerDown
  have hside : (Group.onSide owner side).side = side := by
    cases owner <;> cases side <;> rfl
  have howner : (Group.onSide owner side).upper = owner := by
    cases owner <;> cases side <;> rfl
  change (if down then _ else G) = _
  change attachOwner w _ down cup = some out at hattach
  change (if down then _ else G) = G ⊔ (if down then _ else ⊥)
  by_cases hd : down = true
  · rw [hd] at hattach ⊢
    obtain ⟨older, old, htop, hlast⟩ := attachOwner_down_top hattach
    have hD : (s.word (Group.onSide owner side))[t.processed side]? = some DyckStep.D :=
      (s.nextMove_ownerDown_iff t side owner).mp hd
    have hphysical := s.attachOwner_D_names ht hnext (Group.onSide owner side) hside
      (by simpa only [hside] using hD) port older old (htop ▸ hnames)
    rw [howner] at hphysical
    simp only [ite_true, hlast, Option.getD_some, hphysical.1, hcup]
  · simp only [hd, Bool.false_eq_true, ite_false, sup_bot_eq]

/-- The graph produced by the exact native attachment/drain selections agrees
with the ordered original-source owner edge graphs. -/
theorem Source.physical_visit_graph_eq {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    {w upper attached drained : Splice} (pc qc : Nat) (port : Nat → Incidence spec.n)
    (G : SimpleGraph (Incidence spec.n))
    (hnames : ∀ g, (w.ports.get g).map port = s.retainedGroup ht g)
    (hpc : port pc = (true, s.newPoint hnext))
    (hqc : port qc = (false, s.newPoint hnext))
    (hup : attachOwner w (Group.onSide true side) (s.nextMove t side).upperDown pc = some upper)
    (hlo : attachOwner upper (Group.onSide false side) (s.nextMove t side).lowerDown qc =
      some attached)
    (hdrain : drain (s.joined (t.next side) .pl - s.joined t .pl) .pl .pr attached =
      some drained) :
    let Gp := if (s.nextMove t side).upperDown then
      G ⊔ edge (port ((w.ports.get (Group.onSide true side)).getLast?.getD 0)) (port pc)
      else G
    let Gq := if (s.nextMove t side).lowerDown then
      Gp ⊔ edge (port ((upper.ports.get (Group.onSide false side)).getLast?.getD 0)) (port qc)
      else Gp
    addFifoEdges
      (addFifoEdges Gq port (fifoEdges (s.joined (t.next side) .pl - s.joined t .pl)
        attached.ports .pl .pr)) port
      (fifoEdges (s.joined (t.next side) .ql - s.joined t .ql) drained.ports .ql .qr) =
      G ⊔ s.ownerAttachmentGraph hnext true ⊔ s.ownerAttachmentGraph hnext false ⊔
        s.ownerThroughGraph t side true ⊔ s.ownerThroughGraph t side false := by
  dsimp only
  have hupGraph := s.attachment_graph_eq ht hnext true pc port G (hnames _) hpc hup
  simp only [ite_true] at hupGraph
  rw [hupGraph]
  have hne : Group.onSide false side ≠ Group.onSide true side := by cases side <;> decide
  have hlNames : (upper.ports.get (Group.onSide false side)).map port =
      s.retainedGroup ht (Group.onSide false side) := by
    rw [attachOwner_other_ports hne hup]
    exact hnames _
  have hloGraph := s.attachment_graph_eq ht hnext false qc port
    (G ⊔ s.ownerAttachmentGraph hnext true) hlNames hqc hlo
  simp only [Bool.false_eq_true, ite_false] at hloGraph
  rw [hloGraph]
  have hm := s.attachOwners_groups_map ht hnext pc qc port hnames hpc hqc hup hlo
  have hpGraph := s.addFifoEdges_eq_ownerThrough hnext true
    (G ⊔ s.ownerAttachmentGraph hnext true ⊔ s.ownerAttachmentGraph hnext false)
    port attached.ports (hm .pl) (hm .pr)
  simp only [Group.onSide, ite_true] at hpGraph
  rw [hpGraph]
  have hql : (drained.ports.get .ql).map port = s.beforeDrainGroup t side .ql := by
    rw [drain_small_ports (s.joined_next_between t side .pl).2 (by decide) hdrain]
    simpa using hm .ql
  have hqr : (drained.ports.get .qr).map port = s.beforeDrainGroup t side .qr := by
    rw [drain_small_ports (s.joined_next_between t side .pl).2 (by decide) hdrain]
    simpa using hm .qr
  exact s.addFifoEdges_eq_ownerThrough hnext false _ port drained.ports hql hqr

/-- A complete successful native physical visit preserves the exact original
source graph and retained physical port order. No source connectedness is assumed. -/
theorem Source.RepresentsKey.physical_visit_paths {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x : Key} (hx : s.RepresentsKey ht x)
    (hvalid : validKey spec t x = true) {side : Side} (hnext : s.Progress (t.next side)) :
    let initial : Splice := ⟨Ports.ofLengths (geometry spec t x.counters).length,
      x.mate.map some ++ [some (x.mate.length + 1), some x.mate.length], 0⟩
    ∀ {upper attached drained out : Splice},
      attachOwner initial (Group.onSide true side) (s.nextMove t side).upperDown
        x.mate.length = some upper →
      attachOwner upper (Group.onSide false side) (s.nextMove t side).lowerDown
        (x.mate.length + 1) = some attached →
      drain (s.joined (t.next side) .pl - s.joined t .pl) .pl .pr attached = some drained →
      drain (s.joined (t.next side) .ql - s.joined t .ql) .ql .qr drained = some out →
      MateInvariant out.mate ∧
      RepresentsLivePaths out.mate (s.partialGraph (t.next side)) (s.candidatePort ht hnext) ∧
      out.ports.flat.Nodup ∧ CoversLive out ∧
      ∀ g, (out.ports.get g).map (s.candidatePort ht hnext) = s.retainedGroup hnext g := by
  dsimp only
  intro upper attached drained out hup hlo hpdrain hqdrain
  have hmove := s.nextMove_allowed ht hnext x hx.1
  obtain ⟨hmi, hplive, hpc, hpfresh, hqlive, hqc, hqfresh, hn, hc⟩ :=
    candidate_attachment_facts hvalid hmove hup hlo
  have hpair := (validKey_pairing_contract hvalid).2.1
  have hcup := hx.candidateCup_paths hnext hpair
  obtain ⟨hmout, hpout, hnout, hcout, _, _, _⟩ :=
    FirstCrossing.physical_visit_paths hmi hcup hplive hpc hpfresh hqlive hqc hqfresh
      hup hlo hn hc (s.joined_next_between t side .pl).2
      (s.joined_next_between t side .ql).2 hpdrain hqdrain
  have hnames (g : Group) :
      ((Ports.ofLengths (geometry spec t x.counters).length).get g).map
        (s.candidatePort ht hnext) = s.retainedGroup ht g := by
    rw [hx.1]
    exact s.candidatePort_groups ht hnext g
  have hpcname : s.candidatePort ht hnext x.mate.length = (true, s.newPoint hnext) := by
    rw [hx.2.1, s.candidatePort_upper]
  have hqcname : s.candidatePort ht hnext (x.mate.length + 1) = (false, s.newPoint hnext) := by
    rw [hx.2.1, s.candidatePort_lower]
  have hgraph := s.physical_visit_graph_eq ht hnext x.mate.length (x.mate.length + 1)
    (s.candidatePort ht hnext)
    (s.partialGraph t ⊔ edge (true, s.newPoint hnext) (false, s.newPoint hnext))
    hnames hpcname hqcname hup hlo hpdrain
  dsimp only at hgraph
  rw [hgraph, ← s.partialGraph_next_decomposition ht hnext] at hpout
  have hgroups := s.attachOwners_groups_map ht hnext x.mate.length (x.mate.length + 1)
    (s.candidatePort ht hnext) hnames hpcname hqcname hup hlo
  exact ⟨hmout, hpout, hnout, hcout,
    s.drains_groups_map hnext (s.candidatePort ht hnext) hgroups hpdrain hqdrain⟩

/-- Successful checked surgery represents the original next source graph and
its exact retained groups, irrespective of source connectedness. -/
theorem Source.RepresentsKey.candidateSplice_paths {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x : Key} (hx : s.RepresentsKey ht x)
    (hvalid : validKey spec t x = true) {side : Side} (hnext : s.Progress (t.next side))
    {out : Splice} (h : candidateSplice spec t x side (s.nextMove t side) = some out) :
    MateInvariant out.mate ∧
      RepresentsLivePaths out.mate (s.partialGraph (t.next side)) (s.candidatePort ht hnext) ∧
      out.ports.flat.Nodup ∧ CoversLive out ∧
      ∀ g, (out.ports.get g).map (s.candidatePort ht hnext) = s.retainedGroup hnext g := by
  obtain ⟨_, upper, attached, drained, hup, hlo, _, _, _, hp, hq, _, _⟩ :=
    candidateSplice_factors h
  rw [hx.1, s.nextMove_counters] at hp hq
  change drain (s.joined (t.next side) .pl - s.joined t .pl) .pl .pr attached =
    some drained at hp
  change drain (s.joined (t.next side) .ql - s.joined t .ql) .ql .qr drained = some out at hq
  exact hx.physical_visit_paths hvalid hnext hup hlo hp hq

/-- Every successful canonical candidate preserves the source/key invariant.
Neither successor validity nor source connectedness is a premise. -/
theorem Source.RepresentsKey.candidate {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x y : Key} (hx : s.RepresentsKey ht x)
    (hvalid : validKey spec t x = true) {side : Side} (hnext : s.Progress (t.next side))
    (h : candidate spec t x side (s.nextMove t side) = some y) :
    s.RepresentsKey hnext y := by
  obtain ⟨out, hout, hnorm⟩ := candidate_factors h
  obtain ⟨hm, hp, hn, hc, hgroups⟩ := hx.candidateSplice_paths hvalid hnext hout
  rw [hx.1, s.nextMove_counters] at hnorm
  exact s.normalize_representsKey hnext (s.candidatePort ht hnext) hn hm hc hp hgroups hnorm

/-- A successful actual raw step with the original source label preserves the
shared LOW/HIGH source interpretation. Old validity comes from the raw guard. -/
theorem Source.RepresentsKey.rawStep {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x y : Key} (hx : s.RepresentsKey ht x)
    {side : Side} (hnext : s.Progress (t.next side))
    (hschedule : spec.schedule[t.tick]? = some side)
    (h : rawStep spec t x (s.nextMove t side) = some y) : s.RepresentsKey hnext y := by
  unfold FirstCrossing.rawStep at h
  split at h
  · rename_i hvalid
    rw [hschedule] at h
    cases hc : FirstCrossing.candidate spec t x side (s.nextMove t side) with
    | none => simp [hc] at h
    | some z =>
      simp only [hc] at h
      split at h
      · cases h
        exact hx.candidate hvalid hnext hc
      · contradiction
  · contradiction

/-- The actual native intermediate arrays represent the ordered original
source graph prefixes used to classify each possible closing edge. -/
theorem Source.RepresentsKey.physical_intermediate_paths {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x : Key} (hx : s.RepresentsKey ht x)
    (hvalid : validKey spec t x = true) {side : Side} (hnext : s.Progress (t.next side)) :
    let initial : Splice := ⟨Ports.ofLengths (geometry spec t x.counters).length,
      x.mate.map some ++ [some (x.mate.length + 1), some x.mate.length], 0⟩
    let Gcup := s.partialGraph t ⊔ edge (true, s.newPoint hnext) (false, s.newPoint hnext)
    let Gupper := Gcup ⊔ s.ownerAttachmentGraph hnext true
    let Gattached := Gupper ⊔ s.ownerAttachmentGraph hnext false
    let Gdrained := Gattached ⊔ s.ownerThroughGraph t side true
    ∀ {upper attached drained : Splice},
      attachOwner initial (Group.onSide true side) (s.nextMove t side).upperDown
        x.mate.length = some upper →
      attachOwner upper (Group.onSide false side) (s.nextMove t side).lowerDown
        (x.mate.length + 1) = some attached →
      drain (s.joined (t.next side) .pl - s.joined t .pl) .pl .pr attached = some drained →
      MateInvariant upper.mate ∧
        RepresentsLivePaths upper.mate Gupper (s.candidatePort ht hnext) ∧
      MateInvariant attached.mate ∧
        RepresentsLivePaths attached.mate Gattached (s.candidatePort ht hnext) ∧
      MateInvariant drained.mate ∧
        RepresentsLivePaths drained.mate Gdrained (s.candidatePort ht hnext) := by
  dsimp only
  intro upper attached drained hup hlo hdrain
  have hmove := s.nextMove_allowed ht hnext x hx.1
  obtain ⟨hmi, hplive, hpc, hpfresh, hqlive, hqc, hqfresh, hn, hc⟩ :=
    candidate_attachment_facts hvalid hmove hup hlo
  have hcup := hx.candidateCup_paths hnext (validKey_pairing_contract hvalid).2.1
  have hnames (g : Group) :
      ((Ports.ofLengths (geometry spec t x.counters).length).get g).map
        (s.candidatePort ht hnext) = s.retainedGroup ht g := by
    rw [hx.1]
    exact s.candidatePort_groups ht hnext g
  have hpcname : s.candidatePort ht hnext x.mate.length = (true, s.newPoint hnext) := by
    rw [hx.2.1, s.candidatePort_upper]
  have hqcname : s.candidatePort ht hnext (x.mate.length + 1) = (false, s.newPoint hnext) := by
    rw [hx.2.1, s.candidatePort_lower]
  obtain ⟨hmU, hpU, _⟩ := attachOwner_represents hmi hcup hplive hpc hpfresh hup
  have hgU := s.attachment_graph_eq ht hnext true x.mate.length (s.candidatePort ht hnext)
    (s.partialGraph t ⊔ edge (true, s.newPoint hnext) (false, s.newPoint hnext))
    (hnames _) hpcname hup
  simp only [ite_true] at hgU
  rw [hgU] at hpU
  obtain ⟨hmQ, hpQ, _⟩ := attachOwner_represents hmU hpU hqlive hqc hqfresh hlo
  have hnQ : (upper.ports.get (Group.onSide false side)).map (s.candidatePort ht hnext) =
      s.retainedGroup ht (Group.onSide false side) := by
    rw [attachOwner_other_ports (by cases side <;> decide) hup]
    exact hnames _
  have hgQ := s.attachment_graph_eq ht hnext false (x.mate.length + 1)
    (s.candidatePort ht hnext)
    (s.partialGraph t ⊔ edge (true, s.newPoint hnext) (false, s.newPoint hnext) ⊔
      s.ownerAttachmentGraph hnext true) hnQ hqcname hlo
  simp only [Bool.false_eq_true, ite_false] at hgQ
  rw [hgQ] at hpQ
  obtain ⟨_, _, hmD, _, _, hpD⟩ := drain_small_preserves
    (s.joined_next_between t side .pl).2 (by decide) hn hmQ hc hpQ hdrain
  have hnAttached := s.attachOwners_groups_map ht hnext x.mate.length (x.mate.length + 1)
    (s.candidatePort ht hnext) hnames hpcname hqcname hup hlo
  have hgD := s.addFifoEdges_eq_ownerThrough hnext true
    (s.partialGraph t ⊔ edge (true, s.newPoint hnext) (false, s.newPoint hnext) ⊔
      s.ownerAttachmentGraph hnext true ⊔ s.ownerAttachmentGraph hnext false)
    (s.candidatePort ht hnext)
    attached.ports (hnAttached .pl) (hnAttached .pr)
  simp only [Group.onSide, ite_true] at hgD
  rw [hgD] at hpD
  exact ⟨hmU, hpU, hmQ, hpQ, hmD, hpD⟩

end Meanders.FirstCrossing
