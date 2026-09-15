import Meanders.Models.FirstCrossing.Interpretation.Preservation
import Meanders.Models.FirstCrossing.Interpretation.CycleAcceptance
import Meanders.Models.FirstCrossing.Surgery.ClosingComponent

/-! Exact physical substep degree coverage and cycle acceptance for source visits. -/

namespace Meanders.FirstCrossing

open SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Physical degree coverage is independent of graph presentation and adjacency deciders. -/
theorem RepresentsDegreeOne.congr_graph {V : Type*} [Fintype V]
    {H J : SimpleGraph V} {dH : DecidableRel H.Adj} [dJ : DecidableRel J.Adj]
    {mate : List (Option Nat)} {port : Nat → V}
    (hd : @RepresentsDegreeOne V _ H dH mate port) (he : H = J) :
    RepresentsDegreeOne J mate port := by
  let := dH
  intro v
  have hdeg : H.degree v = J.degree v :=
    le_antisymm (H.degree_le_of_le he.le) (J.degree_le_of_le he.ge)
  rw [← hdeg]
  exact hd v

/-- A physical owner edge cannot be the crossing edge joining the two owners. -/
theorem crossing_not_same_owner {n : Nat} {p : Point n} {a b : Incidence n}
    (howner : a.1 = b.1) : ¬(edge (true, p) (false, p)).Adj a b := by
  intro he
  rcases (edge_adj _ _ _ _).mp he with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, -⟩ <;> cases howner

/-- An internal original attachment cannot be a through edge at the fixed cut. -/
theorem Source.attachment_through_disjoint {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    {owner other : Bool} {a b : Incidence spec.n}
    (ha : (s.ownerAttachmentGraph hnext owner).Adj a b)
    (hf : (s.ownerThroughGraph t side other).Adj a b) : False := by
  have hi := ((s.ownerAttachmentGraph_adj_iff ht hnext owner a b).mp ha).2.2.2.1
  have hj := hf.2.2.2
  simp only [Source.throughAdded] at hj
  rcases hj with ⟨hl, hr, _, _⟩ | ⟨hl, hr, _, _⟩
  · have := hi.mp hl
    omega
  · have := hi.mpr hl
    omega

/-- Each original attachment is distinct from the crossing and the other owner's attachment. -/
theorem Source.attachment_edge_new {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    {owner : Bool} {a b : Incidence spec.n}
    (he : (s.ownerAttachmentGraph hnext owner).Adj a b) :
    ¬(edge (true, s.newPoint hnext) (false, s.newPoint hnext) ⊔
      s.ownerAttachmentGraph hnext (!owner)).Adj a b := by
  have ha := (s.ownerAttachmentGraph_adj_iff ht hnext owner a b).mp he
  rintro (hc | ho)
  · exact crossing_not_same_owner (ha.1.trans ha.2.1.symm) hc
  · have hb := (s.ownerAttachmentGraph_adj_iff ht hnext (!owner) a b).mp ho
    have hh := ha.1.symm.trans hb.1
    cases owner <;> cases hh

/-- A new FIFO edge is distinct from the crossing, both internal attachments,
and the other owner's FIFO edge. Its raw join is therefore physically new. -/
theorem Source.through_edge_new {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    {owner : Bool} {a b : Incidence spec.n}
    (he : (s.ownerThroughGraph t side owner).Adj a b) :
    ¬(edge (true, s.newPoint hnext) (false, s.newPoint hnext) ⊔
      s.ownerAttachmentGraph hnext true ⊔ s.ownerAttachmentGraph hnext false ⊔
      s.ownerThroughGraph t side (!owner)).Adj a b := by
  rintro (((hc | hp) | hq) | ho)
  · exact crossing_not_same_owner (he.1.trans he.2.1.symm) hc
  · exact s.attachment_through_disjoint ht hnext hp he
  · exact s.attachment_through_disjoint ht hnext hq he
  · have hh := he.1.symm.trans ho.1
    cases owner <;> cases hh

/-- The initial candidate cup has exact degree-one coverage in the actual source graph. -/
theorem Source.RepresentsKey.candidateCup_degreeOne {spec : RunSpec} {s : Source spec}
    {t : Stage} {side : Side} {ht : s.Progress t} (hnext : s.Progress (t.next side))
    {x : Key} (hx : s.RepresentsKey ht x) :
    RepresentsDegreeOne
      (s.partialGraph t ⊔ edge (true, s.newPoint hnext) (false, s.newPoint hnext))
      (x.mate.map some ++ [some (x.mate.length + 1), some x.mate.length])
      (s.candidatePort ht hnext) := by
  classical
  have hport := s.candidatePort_old ht hnext
  have hd := (hx.degreeOne hport).1
  have hp : s.candidatePort ht hnext x.mate.length = (true, s.newPoint hnext) := by
    rw [hx.2.1, s.candidatePort_upper]
  have hq : s.candidatePort ht hnext (x.mate.length + 1) = (false, s.newPoint hnext) := by
    rw [hx.2.1, s.candidatePort_lower]
  have hd0 (owner : Bool) : (s.partialGraph t).degree (owner, s.newPoint hnext) = 0 := by
    have hh := s.partialGraph_degree t (owner, s.newPoint hnext)
    simpa only [s.newPoint_not_visited hnext, ite_false] using hh
  have hn : s.candidatePort ht hnext x.mate.length ≠
      s.candidatePort ht hnext (x.mate.length + 1) := by rw [hp, hq]; simp
  have hc := FirstCrossing.candidateCup_degreeOne hd hn (by rw [hp]; exact hd0 true)
    (by rw [hq]; exact hd0 false)
  simpa only [hp, hq] using hc

/-- Every still-live temporary name lies in the injective physical candidate boundary. -/
theorem Source.candidatePort_live_injective {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    {mate : List (Option Nat)}
    (hlen : mate.length ≤ (s.retainedBoundary ht).length + 2) :
    Set.InjOn (s.candidatePort ht hnext) {i | Live mate i} := by
  intro i hi j hj he
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb⟩ := hj
  exact s.candidatePort_injective ht hnext (ha.bound.trans_le hlen)
    (hb.bound.trans_le hlen) he

/-- One actual owner slot propagates physical degrees and derives its cycle facts
from original D names and source-edge disjointness. -/
theorem Source.attachment_slot_degree_cycle {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (owner : Bool) {E : SimpleGraph (Incidence spec.n)} [dE : DecidableRel E.Adj]
    (hE : E ≤ s.visitEdges hnext)
    (hprior : E ≤ edge (true, s.newPoint hnext) (false, s.newPoint hnext) ⊔
      s.ownerAttachmentGraph hnext (!owner))
    {w out : Splice} {cup : Nat} {port : Nat → Incidence spec.n}
    (hnames : (w.ports.get (Group.onSide owner side)).map port =
      s.retainedGroup ht (Group.onSide owner side))
    (hcupname : port cup = (owner, s.newPoint hnext))
    (hm : MateInvariant w.mate)
    (hd : RepresentsDegreeOne (s.partialGraph t ⊔ E) w.mate port)
    (hp : RepresentsLivePaths w.mate (s.partialGraph t ⊔ E) port)
    (hinj : Set.InjOn port {i | Live w.mate i})
    (hlive : ∀ i ∈ w.ports.get (Group.onSide owner side), Live w.mate i)
    (hcup : Live w.mate cup) (hfresh : cup ∉ w.ports.get (Group.onSide owner side))
    (hconn : (incidenceGraph s.matchings).Connected)
    (hattach : attachOwner w (Group.onSide owner side)
      (if owner then (s.nextMove t side).upperDown else (s.nextMove t side).lowerDown)
      cup = some out) :
    RepresentsDegreeOne (s.partialGraph t ⊔ E ⊔ s.ownerAttachmentGraph hnext owner)
      out.mate port ∧
    CycleStepFacts s (t.next side) (s.partialGraph t ⊔ E)
      (s.partialGraph t ⊔ E ⊔ s.ownerAttachmentGraph hnext owner) w.cycles out.cycles := by
  classical
  let down := if owner then (s.nextMove t side).upperDown else (s.nextMove t side).lowerDown
  change attachOwner w _ down cup = some out at hattach
  have hside : (Group.onSide owner side).side = side := by cases owner <;> cases side <;> rfl
  have howner : (Group.onSide owner side).upper = owner := by cases owner <;> cases side <;> rfl
  cases hdown : down with
  | false =>
    have hcycles : out.cycles = w.cycles := attachOwner_up_cycles (hdown ▸ hattach)
    have hmate : out.mate = w.mate := by
      simp only [hdown, attachOwner, Bool.false_eq_true, ite_false, Option.some.injEq] at hattach
      subst out
      rfl
    have he : s.ownerAttachmentGraph hnext owner = ⊥ := by
      change (if down then _ else _) = _
      simp only [hdown, Bool.false_eq_true, ite_false]
    refine ⟨?_, CycleStepFacts.of_unchanged hcycles⟩
    rw [hmate]
    exact hd.congr_graph (by rw [he, sup_bot_eq])
  | true =>
    have hD := (s.nextMove_ownerDown_iff t side owner).mp hdown
    obtain ⟨older, old, htop, -⟩ := attachOwner_down_top (hdown ▸ hattach)
    have hnames' : (older ++ [old]).map port = s.retainedGroup ht (Group.onSide owner side) :=
      htop ▸ hnames
    have hD' : (s.word (Group.onSide owner side))[t.processed (Group.onSide owner side).side]? =
        some DyckStep.D := by simpa only [hside] using hD
    have hold := (s.attachOwner_D_names ht hnext (Group.onSide owner side) hside hD'
      port older old hnames').1
    rw [howner] at hold
    have he : s.ownerAttachmentGraph hnext owner = edge (port old) (port cup) := by
      change (if down then _ else _) = _
      simp only [hdown, ite_true, hold, hcupname]
    have hedge : (s.ownerAttachmentGraph hnext owner).Adj (port old) (port cup) := by
      rw [he]
      exact (edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, by
        rw [hold, hcupname]
        intro hh
        exact (ownerMatching s.matchings owner).partner_ne _ (congrArg Prod.snd hh)⟩
    have hnot : ¬ E.Adj (port old) (port cup) :=
      fun hh => s.attachment_edge_new ht hnext hedge (hprior hh)
    have hvisit : (s.visitEdges hnext).Adj (port old) (port cup) := by
      rw [s.visitEdges_decomposition ht hnext]
      cases owner
      · exact Or.inl (Or.inl (Or.inr hedge))
      · exact Or.inl (Or.inl (Or.inl (Or.inr hedge)))
    have hmem : old ∈ w.ports.get (Group.onSide owner side) := by simp [htop]
    obtain ⟨a, ha⟩ := hlive old hmem
    obtain ⟨b, hb⟩ := hcup
    have hne : old ≠ cup := by rintro rfl; exact hfresh hmem
    have hj := hattach
    rw [hdown, attachOwner_down_eq w _ cup old older htop] at hj
    have hdout := spliceJoin_degreeOne (w := {w with ports := w.ports.set _ older})
      hm hd hinj ha hb hne (s.visit_edge_new_after_prefix hnext hvisit hnot) hj
    have hcf := s.visit_splice_cycle_facts ht hnext hE
      (w := {w with ports := w.ports.set _ older}) hm hd hp hconn ha hb hne hvisit hnot hj
    exact ⟨hdout.congr_graph (by rw [he]), by simpa only [he] using hcf⟩

/-- The actual zero-or-one FIFO slot propagates degrees and cycle facts on its
original source through edge, with no successor interpretation premise. -/
theorem Source.drain_slot_degree_cycle {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (owner : Bool) {E : SimpleGraph (Incidence spec.n)} [dE : DecidableRel E.Adj]
    (hE : E ≤ s.visitEdges hnext)
    (hprior : E ≤ edge (true, s.newPoint hnext) (false, s.newPoint hnext) ⊔
      s.ownerAttachmentGraph hnext true ⊔ s.ownerAttachmentGraph hnext false ⊔
      s.ownerThroughGraph t side (!owner))
    {w out : Splice} {port : Nat → Incidence spec.n}
    (hnamesL : (w.ports.get (Group.onSide owner .left)).map port =
      s.beforeDrainGroup t side (Group.onSide owner .left))
    (hnamesR : (w.ports.get (Group.onSide owner .right)).map port =
      s.beforeDrainGroup t side (Group.onSide owner .right))
    (hm : MateInvariant w.mate)
    (hd : RepresentsDegreeOne (s.partialGraph t ⊔ E) w.mate port)
    (hp : RepresentsLivePaths w.mate (s.partialGraph t ⊔ E) port)
    (hinj : Set.InjOn port {i | Live w.mate i})
    (hn : w.ports.flat.Nodup) (hc : CoversLive w)
    (hconn : (incidenceGraph s.matchings).Connected)
    (hjoin : drain (s.joined (t.next side) (Group.onSide owner .left) -
      s.joined t (Group.onSide owner .left)) (Group.onSide owner .left)
      (Group.onSide owner .right) w = some out) :
    RepresentsDegreeOne (s.partialGraph t ⊔ E ⊔ s.ownerThroughGraph t side owner)
      out.mate port ∧
    CycleStepFacts s (t.next side) (s.partialGraph t ⊔ E)
      (s.partialGraph t ⊔ E ⊔ s.ownerThroughGraph t side owner) w.cycles out.cycles := by
  classical
  have hdelta := (s.joined_next_between t side (Group.onSide owner .left)).2
  rcases (show s.joined (t.next side) (Group.onSide owner .left) -
      s.joined t (Group.onSide owner .left) = 0 ∨
      s.joined (t.next side) (Group.onSide owner .left) -
      s.joined t (Group.onSide owner .left) = 1 by omega) with hz | hone
  · rw [hz, drain_zero] at hjoin
    cases hjoin
    have he := s.ownerThroughGraph_eq_bot t side owner hz
    exact ⟨hd.congr_graph (by rw [he, sup_bot_eq]), CycleStepFacts.of_unchanged rfl⟩
  · rw [hone] at hjoin
    obtain ⟨x, xs, y, ys, hl, hr, hj⟩ := drain_one_success hjoin
    have hxy : x ≠ y := Ports.heads_ne hn (by cases owner <;> decide) hl hr
    obtain ⟨a, ha⟩ := (hc x).mp
      ((Ports.mem_flat_iff _ _).mpr ⟨Group.onSide owner .left, by simp [hl]⟩)
    obtain ⟨b, hb⟩ := (hc y).mp
      ((Ports.mem_flat_iff _ _).mpr ⟨Group.onSide owner .right, by simp [hr]⟩)
    have hphys : port x ≠ port y := fun he => hxy (hinj ⟨a, ha⟩ ⟨b, hb⟩ he)
    have hgraph := s.addFifoEdges_eq_ownerThrough hnext owner ⊥ port w.ports hnamesL hnamesR
    simp only [hone, fifoEdges_one hl hr, addFifoEdges, List.foldl_cons, List.foldl_nil,
      bot_sup_eq] at hgraph
    have hedge : (s.ownerThroughGraph t side owner).Adj (port x) (port y) := by
      rw [← hgraph]
      exact (edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hphys⟩
    have hnot : ¬ E.Adj (port x) (port y) :=
      fun hh => s.through_edge_new ht hnext hedge (hprior hh)
    have hvisit : (s.visitEdges hnext).Adj (port x) (port y) := by
      rw [s.visitEdges_decomposition ht hnext]
      cases owner
      · exact Or.inr hedge
      · exact Or.inl (Or.inr hedge)
    have hdout := spliceJoin_degreeOne
      (w := {w with ports := w.ports.popHeads _ _}) hm hd hinj ha hb hxy
      (s.visit_edge_new_after_prefix hnext hvisit hnot) hj
    have hcf := s.visit_splice_cycle_facts ht hnext hE
      (w := {w with ports := w.ports.popHeads _ _}) hm hd hp hconn ha hb hxy hvisit hnot hj
    exact ⟨hdout.congr_graph (by rw [hgraph]), by simpa only [hgraph] using hcf⟩

set_option maxHeartbeats 1600000 in
-- Concrete graph prefixes and adjacency instances require additional reduction.
/-- All four actual source slots satisfy cycle acceptance from the original
represented input. Substep degrees and edge newness are derived here. -/
theorem Source.RepresentsKey.physical_visit_cycleAccepted {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x : Key} (hx : s.RepresentsKey ht x)
    (hvalid : validKey spec t x = true) {side : Side} (hnext : s.Progress (t.next side))
    (hconn : (incidenceGraph s.matchings).Connected)
    (htick : (t.next side).tick = (t.next side).left + (t.next side).right) :
    let initial : Splice := ⟨Ports.ofLengths (geometry spec t x.counters).length,
      x.mate.map some ++ [some (x.mate.length + 1), some x.mate.length], 0⟩
    ∀ {upper attached drained out : Splice},
      attachOwner initial (Group.onSide true side) (s.nextMove t side).upperDown
        x.mate.length = some upper →
      attachOwner upper (Group.onSide false side) (s.nextMove t side).lowerDown
        (x.mate.length + 1) = some attached →
      drain (s.joined (t.next side) .pl - s.joined t .pl) .pl .pr attached = some drained →
      drain (s.joined (t.next side) .ql - s.joined t .ql) .ql .qr drained = some out →
      CyclicFrontier out.mate out.ports.cyclic → CycleAccepted spec (t.next side) out := by
  classical
  dsimp only
  intro upper attached drained out hup hlo hpdrain hqdrain hf
  let initial : Splice := ⟨Ports.ofLengths (geometry spec t x.counters).length,
    x.mate.map some ++ [some (x.mate.length + 1), some x.mate.length], 0⟩
  let port := s.candidatePort ht hnext
  let C := edge (true, s.newPoint hnext) (false, s.newPoint hnext)
  let A := s.ownerAttachmentGraph hnext true
  let B := s.ownerAttachmentGraph hnext false
  let P := s.ownerThroughGraph t side true
  let Q := s.ownerThroughGraph t side false
  have hdecomp : s.visitEdges hnext = C ⊔ A ⊔ B ⊔ P ⊔ Q :=
    s.visitEdges_decomposition ht hnext
  have hC : C ≤ s.visitEdges hnext := by
    rw [hdecomp]
    exact le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))
  have hA : C ⊔ A ≤ s.visitEdges hnext := by
    rw [hdecomp]
    exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hB : C ⊔ A ⊔ B ≤ s.visitEdges hnext := by
    rw [hdecomp]
    exact le_sup_left.trans le_sup_left
  have hP : C ⊔ A ⊔ B ⊔ P ≤ s.visitEdges hnext := by rw [hdecomp]; exact le_sup_left
  have hmove := s.nextMove_allowed ht hnext x hx.1
  obtain ⟨hmi, hplive, hpc, hpfresh, hqlive, hqc, hqfresh, hn, hc⟩ :=
    candidate_attachment_facts hvalid hmove hup hlo
  have hcup := hx.candidateCup_paths hnext (validKey_pairing_contract hvalid).2.1
  obtain ⟨hmU, hpU, hmA, hpA, hmD, hpD⟩ :=
    hx.physical_intermediate_paths hvalid hnext hup hlo hpdrain
  have hnames (g : Group) : (initial.ports.get g).map port = s.retainedGroup ht g := by
    change ((Ports.ofLengths (geometry spec t x.counters).length).get g).map _ = _
    rw [hx.1]
    exact s.candidatePort_groups ht hnext g
  have hpcname : port x.mate.length = (true, s.newPoint hnext) := by
    change s.candidatePort ht hnext _ = _
    rw [hx.2.1, s.candidatePort_upper]
  have hqcname : port (x.mate.length + 1) = (false, s.newPoint hnext) := by
    change s.candidatePort ht hnext _ = _
    rw [hx.2.1, s.candidatePort_lower]
  have hiLen : initial.mate.length = (s.retainedBoundary ht).length + 2 := by
    simp [initial, hx.2.1]
  have huLen := (attachOwner_represents hmi hcup hplive hpc hpfresh hup).2.2
  have haLen := (attachOwner_represents hmU hpU hqlive hqc hqfresh hlo).2.2
  have hiInj := s.candidatePort_live_injective ht hnext hiLen.le
  have huInj := s.candidatePort_live_injective ht hnext (huLen.trans hiLen).le
  have haInj := s.candidatePort_live_injective ht hnext (haLen.trans (huLen.trans hiLen)).le
  have hdCup := hx.candidateCup_degreeOne hnext
  obtain ⟨hdU, cfU⟩ := s.attachment_slot_degree_cycle ht hnext true hC le_sup_left
    (hnames _) hpcname hmi hdCup hcup hiInj hplive hpc hpfresh hconn hup
  have hLowerNames : (upper.ports.get (Group.onSide false side)).map port =
      s.retainedGroup ht (Group.onSide false side) := by
    rw [attachOwner_other_ports (by cases side <;> decide) hup]
    exact hnames _
  have hdU' : RepresentsDegreeOne (s.partialGraph t ⊔ (C ⊔ A)) upper.mate port :=
    hdU.congr_graph (by simp only [C, A, sup_assoc])
  have hpU' : RepresentsLivePaths upper.mate (s.partialGraph t ⊔ (C ⊔ A)) port := by
    simpa only [C, A, sup_assoc] using hpU
  obtain ⟨hdA, cfA⟩ := s.attachment_slot_degree_cycle ht hnext false hA le_rfl
    hLowerNames hqcname hmU hdU' hpU' huInj hqlive hqc hqfresh hconn hlo
  have hAttachedNames := s.attachOwners_groups_map ht hnext x.mate.length (x.mate.length + 1)
    port hnames hpcname hqcname hup hlo
  have hdA' : RepresentsDegreeOne (s.partialGraph t ⊔ (C ⊔ A ⊔ B)) attached.mate port :=
    hdA.congr_graph (by simp only [C, A, B, sup_assoc])
  have hpA' : RepresentsLivePaths attached.mate (s.partialGraph t ⊔ (C ⊔ A ⊔ B)) port := by
    simpa only [C, A, B, sup_assoc] using hpA
  obtain ⟨hdD, cfD⟩ := s.drain_slot_degree_cycle ht hnext true hB le_sup_left
    (hAttachedNames .pl) (hAttachedNames .pr) hmA hdA' hpA' haInj hn hc hconn hpdrain
  obtain ⟨_, hnD, _, hcD, hdLen, _⟩ := drain_small_preserves
    (s.joined_next_between t side .pl).2 (by decide) hn hmA hc hpA hpdrain
  have hdInj := s.candidatePort_live_injective ht hnext
    (hdLen.trans (haLen.trans (huLen.trans hiLen))).le
  have hDNames (g : Group) (hg : g = .ql ∨ g = .qr) :
      (drained.ports.get g).map port = s.beforeDrainGroup t side g := by
    rw [drain_small_ports (s.joined_next_between t side .pl).2 (by decide) hpdrain]
    rcases hg with rfl | rfl <;> simpa using hAttachedNames _
  have hdD' : RepresentsDegreeOne (s.partialGraph t ⊔ (C ⊔ A ⊔ B ⊔ P)) drained.mate port :=
    hdD.congr_graph (by simp only [C, A, B, P, sup_assoc])
  have hpD' : RepresentsLivePaths drained.mate (s.partialGraph t ⊔ (C ⊔ A ⊔ B ⊔ P)) port := by
    simpa only [C, A, B, P, sup_assoc] using hpD
  let dE : DecidableRel (C ⊔ A ⊔ B ⊔ P).Adj := Classical.decRel _
  let dH : DecidableRel (s.partialGraph t ⊔ (C ⊔ A ⊔ B ⊔ P)).Adj :=
    fun a b => @Sup.adjDecidable _ _ _ inferInstance dE a b
  obtain ⟨hdOut, cfOut⟩ := s.drain_slot_degree_cycle (dE := dE) ht hnext false hP le_rfl
    (hDNames .ql (Or.inl rfl)) (hDNames .qr (Or.inr rfl))
    hmD (hdD'.congr_graph (dJ := dH) rfl) hpD' hdInj hnD hcD
      hconn hqdrain
  have hlast : s.partialGraph t ⊔ C ⊔ A ⊔ B ⊔ P ⊔ Q = s.partialGraph (t.next side) :=
    (s.partialGraph_next_decomposition ht hnext).symm
  apply s.cycleAccepted_of_four_slots (t.next side) (c₀ := 0)
    (H₀ := s.partialGraph t ⊔ C) (H₁ := s.partialGraph t ⊔ C ⊔ A)
    (H₂ := s.partialGraph t ⊔ C ⊔ A ⊔ B) (H₃ := s.partialGraph t ⊔ C ⊔ A ⊔ B ⊔ P)
    (H₄ := s.partialGraph t ⊔ C ⊔ A ⊔ B ⊔ P ⊔ Q)
    rfl htick cfU
    (by simpa only [C, A, B, sup_assoc] using cfA)
    (by simpa only [C, A, B, P, sup_assoc] using cfD)
    (by simpa only [C, A, B, P, Q, sup_assoc] using cfOut)
    le_sup_left le_sup_left le_sup_left le_sup_left
    (hlast ▸ s.partialGraph_le (t.next side)) hf
  exact hdOut.congr_graph (by simp only [C, A, B, P, Q, sup_assoc])

/-- A connected complete source has an actual native successor for its original
next label. All cycle, geometry, normalization, and output guards are discharged. -/
theorem Source.RepresentsKey.nextMove_total {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x : Key} (hx : s.RepresentsKey ht x)
    (hvalid : validKey spec t x = true) {side : Side} (hnext : s.Progress (t.next side))
    (hschedule : spec.schedule[t.tick]? = some side)
    (hconn : (unionGraph s.matchings).Connected) :
    ∃ y, FirstCrossing.rawStep spec t x (s.nextMove t side) = some y ∧ s.RepresentsKey hnext y := by
  have hmove := s.nextMove_allowed ht hnext x hx.1
  obtain ⟨upper, attached, drained, out, hup, hlo, hpdrain, hqdrain, hf, hl, hb, hw⟩ :=
    candidateSplice_stages hvalid hmove
  have hp := hpdrain
  have hq := hqdrain
  rw [hx.1, s.nextMove_counters] at hp hq
  change drain (s.joined (t.next side) .pl - s.joined t .pl) .pl .pr attached =
    some drained at hp
  change drain (s.joined (t.next side) .ql - s.joined t .ql) .ql .qr drained = some out at hq
  have hg := hvalid
  simp only [validKey, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨hs, htvalid⟩, hc⟩, hpref⟩, -⟩, -⟩, -⟩ := hg
  have htv := of_decide_eq_true htvalid
  have hsum := s.ofTick_sum htv.1
  rw [← htv.2] at hsum
  have htick : (t.next side).tick = (t.next side).left + (t.next side).right := by
    cases side <;> simp only [Stage.next] <;> omega
  have ha := hx.physical_visit_cycleAccepted hvalid hnext
    ((incidenceGraph_connected_iff s.matchings).mpr hconn) htick hup hlo hp hq hf
  have hw' : candidateSplice spec t x side (s.nextMove t side) = some out := by
    simpa only [ha, ite_true] using hw
  obtain ⟨y, hy⟩ := normalize_total hf.flat.1 hf.pairing hf.flat.2
    (moveCounters x.counters side (s.nextMove t side))
  have hyvalid := normalize_validKey hs (Stage.valid_next hs htvalid hschedule)
    (moveAllowed_countersValid hc hmove) (moveAllowed_prefixAllowed hpref hmove) hf hl hb ha hy
  have hcand : FirstCrossing.candidate spec t x side (s.nextMove t side) = some y := by
    simp only [FirstCrossing.candidate, hw', Option.bind_some, hy]
  have hraw : FirstCrossing.rawStep spec t x (s.nextMove t side) = some y := by
    simp only [FirstCrossing.rawStep, hvalid, ite_true, hschedule, hcand, hyvalid]
  exact ⟨y, hraw, hx.rawStep hnext hschedule hraw⟩

end Meanders.FirstCrossing
