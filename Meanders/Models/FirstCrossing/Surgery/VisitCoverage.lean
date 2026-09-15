import Meanders.Models.FirstCrossing.Surgery.Drain
import Meanders.Models.FirstCrossing.Surgery.Cup
import Meanders.Models.FirstCrossing.Surgery.Coverage

/-!
# Physical paths under a successful owner attachment

The endpoint is read from the actual newest group slot. Pending cup names need
not belong to a port group yet, so the input only requires existing group
members to be live.
-/

namespace Meanders.FirstCrossing

open SimpleGraph

/-- A successful down attachment selects the actual newest group endpoint. -/
theorem attachOwner_down_top {w out : Splice} {g : Group} {cup : Nat}
    (h : attachOwner w g true cup = some out) :
    ∃ older old, w.ports.get g = older ++ [old] ∧
      (w.ports.get g).getLast? = some old := by
  cases hr : (w.ports.get g).reverse with
  | nil => simp [attachOwner, hr] at h
  | cons old older =>
    have ht : w.ports.get g = older.reverse ++ [old] := by
      simpa using congrArg List.reverse hr
    exact ⟨older.reverse, old, ht, by simp [ht]⟩

/-- The successful operation preserves physical paths after adding precisely the
owner edge chosen by its newest port, or leaves the graph unchanged for an opening. -/
theorem attachOwner_represents {V : Type*} {w out : Splice} {g : Group}
    {down : Bool} {cup : Nat} {G : SimpleGraph V} {port : Nat → V}
    (hm : MateInvariant w.mate) (hp : RepresentsLivePaths w.mate G port)
    (hlive : ∀ x ∈ w.ports.get g, Live w.mate x) (hcup : Live w.mate cup)
    (hfresh : cup ∉ w.ports.get g) (h : attachOwner w g down cup = some out) :
    MateInvariant out.mate ∧
      RepresentsLivePaths out.mate
        (if down then G ⊔ edge (port ((w.ports.get g).getLast?.getD 0)) (port cup)
          else G) port ∧
      out.mate.length = w.mate.length := by
  cases down with
  | false =>
    obtain ⟨-, he, -, hm', hp'⟩ := attachOwner_up_result hm hp h
    exact ⟨hm', hp', congrArg List.length he⟩
  | true =>
    obtain ⟨older, old, ht, hlast⟩ := attachOwner_down_top h
    have hmem : old ∈ w.ports.get g := by simp [ht]
    obtain ⟨a, ha⟩ := hlive old hmem
    obtain ⟨b, hb⟩ := hcup
    have hne : old ≠ cup := by rintro rfl; exact hfresh hmem
    obtain ⟨hm', hp', -, -, hlen, -⟩ :=
      attachOwner_down_result ht hm hp ha hb hne h
    exact ⟨hm', by simpa [hlast] using hp', hlen⟩

/-- Successful owner attachment retains witnesses for processed components and
keeps their number equal to the actual executable cycle counter. -/
theorem attachOwner_covers {V : Type*} {w out : Splice} {g : Group}
    {down : Bool} {cup : Nat} {G : SimpleGraph V} {port : Nat → V}
    {closed : List V} {processed : V → Prop}
    (hm : MateInvariant w.mate) (hp : RepresentsLivePaths w.mate G port)
    (hc : CoversProcessed w.mate G port closed processed)
    (hcount : closed.length = w.cycles)
    (hlive : ∀ x ∈ w.ports.get g, Live w.mate x) (hcup : Live w.mate cup)
    (hfresh : cup ∉ w.ports.get g) (h : attachOwner w g down cup = some out) :
    ∃ closed', CoversProcessed out.mate
      (if down then G ⊔ edge (port ((w.ports.get g).getLast?.getD 0)) (port cup)
        else G) port closed' processed ∧ closed'.length = out.cycles := by
  cases down with
  | false =>
    obtain ⟨-, he, hcycles, -, -⟩ := attachOwner_up_result hm hp h
    exact ⟨closed, by simpa [he] using hc, hcount.trans hcycles.symm⟩
  | true =>
    obtain ⟨older, old, ht, hlast⟩ := attachOwner_down_top h
    have hmem : old ∈ w.ports.get g := by simp [ht]
    obtain ⟨a, ha⟩ := hlive old hmem
    obtain ⟨b, hb⟩ := hcup
    have hne : old ≠ cup := by rintro rfl; exact hfresh hmem
    rw [attachOwner_down_eq w g cup old older ht] at h
    obtain ⟨closed', hc', hcount', -⟩ :=
      spliceJoin_covers (w := {w with ports := w.ports.set g older})
        hm hp hc hcount ha hb hne h
    exact ⟨closed', by simpa [hlast] using hc', hcount'⟩

end Meanders.FirstCrossing

/-!
# Closed-component coverage through a complete physical visit

This module composes the existing actual cup, owner attachment, and FIFO drain
operations. Closed witnesses remain proof-only data and track exact cycle counts.
-/

namespace Meanders.FirstCrossing

open SimpleGraph

/-- The actual upper attachment, lower attachment and two ordered FIFO drains
preserve physical paths without any assumption on components with no live ports. -/
theorem physical_visit_paths {V : Type*} {w upper attached drained out : Splice}
    {G : SimpleGraph V} {port : Nat → V}
    {side : Side} {m : Move} {pc qc kp kq : Nat}
    (hm : MateInvariant w.mate) (hp : RepresentsLivePaths w.mate G port)
    (hplive : ∀ x ∈ w.ports.get (Group.onSide true side), Live w.mate x)
    (hpc : Live w.mate pc) (hpfresh : pc ∉ w.ports.get (Group.onSide true side))
    (hqlive : ∀ x ∈ upper.ports.get (Group.onSide false side), Live upper.mate x)
    (hqc : Live upper.mate qc)
    (hqfresh : qc ∉ upper.ports.get (Group.onSide false side))
    (hpattach : attachOwner w (Group.onSide true side) m.upperDown pc = some upper)
    (hqattach : attachOwner upper (Group.onSide false side) m.lowerDown qc = some attached)
    (hn : attached.ports.flat.Nodup) (hl : CoversLive attached)
    (hkp : kp ≤ 1) (hkq : kq ≤ 1)
    (hpdrain : drain kp .pl .pr attached = some drained)
    (hqdrain : drain kq .ql .qr drained = some out) :
    let Gp := if m.upperDown then
      G ⊔ edge (port ((w.ports.get (Group.onSide true side)).getLast?.getD 0)) (port pc)
      else G
    let Gq := if m.lowerDown then
      Gp ⊔ edge (port ((upper.ports.get (Group.onSide false side)).getLast?.getD 0))
        (port qc) else Gp
    let GpDrain := addFifoEdges Gq port (fifoEdges kp attached.ports .pl .pr)
    let Gout := addFifoEdges GpDrain port (fifoEdges kq drained.ports .ql .qr)
    MateInvariant out.mate ∧ RepresentsLivePaths out.mate Gout port ∧
      out.ports.flat.Nodup ∧ CoversLive out ∧ out.mate.length = w.mate.length ∧
      (∀ g, drained.ports.get g = if g = .pl ∨ g = .pr
        then (attached.ports.get g).drop kp else attached.ports.get g) ∧
      (∀ g, out.ports.get g = if g = .ql ∨ g = .qr
        then (drained.ports.get g).drop kq else drained.ports.get g) := by
  obtain ⟨hmP, hpP, hlenP⟩ := attachOwner_represents hm hp hplive hpc hpfresh hpattach
  obtain ⟨hmQ, hpQ, hlenQ⟩ := attachOwner_represents hmP hpP hqlive hqc hqfresh hqattach
  obtain ⟨hportsP, hnP, hmPD, hlP, hlenPD, hpPD⟩ :=
    drain_small_preserves hkp (by decide) hn hmQ hl hpQ hpdrain
  obtain ⟨hportsQ, hnQ, hmQD, hlQ, hlenQD, hpQD⟩ :=
    drain_small_preserves hkq (by decide) hnP hmPD hlP hpPD hqdrain
  exact ⟨hmQD, hpQD, hnQ, hlQ, hlenQD.trans (hlenPD.trans (hlenQ.trans hlenP)),
    hportsP, hportsQ⟩

/-- The actual upper attachment, lower attachment and two ordered FIFO drains
preserve physical paths and processed-component coverage in one shared chain. -/
theorem physical_visit_preserves {V : Type*} {w upper attached drained out : Splice}
    {G : SimpleGraph V} {port : Nat → V} {closed : List V} {processed : V → Prop}
    {side : Side} {m : Move} {pc qc kp kq : Nat}
    (hm : MateInvariant w.mate) (hp : RepresentsLivePaths w.mate G port)
    (hc : CoversProcessed w.mate G port closed processed)
    (hcount : closed.length = w.cycles)
    (hplive : ∀ x ∈ w.ports.get (Group.onSide true side), Live w.mate x)
    (hpc : Live w.mate pc) (hpfresh : pc ∉ w.ports.get (Group.onSide true side))
    (hqlive : ∀ x ∈ upper.ports.get (Group.onSide false side), Live upper.mate x)
    (hqc : Live upper.mate qc)
    (hqfresh : qc ∉ upper.ports.get (Group.onSide false side))
    (hpattach : attachOwner w (Group.onSide true side) m.upperDown pc = some upper)
    (hqattach : attachOwner upper (Group.onSide false side) m.lowerDown qc = some attached)
    (hn : attached.ports.flat.Nodup) (hl : CoversLive attached)
    (hkp : kp ≤ 1) (hkq : kq ≤ 1)
    (hpdrain : drain kp .pl .pr attached = some drained)
    (hqdrain : drain kq .ql .qr drained = some out) :
    let Gp := if m.upperDown then
      G ⊔ edge (port ((w.ports.get (Group.onSide true side)).getLast?.getD 0)) (port pc)
      else G
    let Gq := if m.lowerDown then
      Gp ⊔ edge (port ((upper.ports.get (Group.onSide false side)).getLast?.getD 0))
        (port qc) else Gp
    let GpDrain := addFifoEdges Gq port (fifoEdges kp attached.ports .pl .pr)
    let Gout := addFifoEdges GpDrain port (fifoEdges kq drained.ports .ql .qr)
    MateInvariant out.mate ∧ RepresentsLivePaths out.mate Gout port ∧
      out.ports.flat.Nodup ∧ CoversLive out ∧ out.mate.length = w.mate.length ∧
      (∀ g, drained.ports.get g = if g = .pl ∨ g = .pr
        then (attached.ports.get g).drop kp else attached.ports.get g) ∧
      (∀ g, out.ports.get g = if g = .ql ∨ g = .qr
        then (drained.ports.get g).drop kq else drained.ports.get g) ∧
      ∃ closed', CoversProcessed out.mate Gout port closed' processed ∧
        closed'.length = out.cycles := by
  obtain ⟨hmP, hpP, hlenP⟩ := attachOwner_represents hm hp hplive hpc hpfresh hpattach
  obtain ⟨closedP, hcP, hcountP⟩ :=
    attachOwner_covers hm hp hc hcount hplive hpc hpfresh hpattach
  obtain ⟨hmQ, hpQ, hlenQ⟩ := attachOwner_represents hmP hpP hqlive hqc hqfresh hqattach
  obtain ⟨closedQ, hcQ, hcountQ⟩ :=
    attachOwner_covers hmP hpP hcP hcountP hqlive hqc hqfresh hqattach
  obtain ⟨hportsP, hnP, hmPD, hlP, hlenPD, hpPD⟩ :=
    drain_small_preserves hkp (by decide) hn hmQ hl hpQ hpdrain
  obtain ⟨closedPD, hcPD, hcountPD⟩ :=
    drain_small_covers hkp (by decide) hn hmQ hl hpQ hcQ hcountQ hpdrain
  obtain ⟨hportsQ, hnQ, hmQD, hlQ, hlenQD, hpQD⟩ :=
    drain_small_preserves hkq (by decide) hnP hmPD hlP hpPD hqdrain
  obtain ⟨closedQD, hcQD, hcountQD⟩ :=
    drain_small_covers hkq (by decide) hnP hmPD hlP hpPD hcPD hcountPD hqdrain
  exact ⟨hmQD, hpQD, hnQ, hlQ, hlenQD.trans (hlenPD.trans (hlenQ.trans hlenP)),
    hportsP, hportsQ, closedQD, hcQD, hcountQD⟩

end Meanders.FirstCrossing
