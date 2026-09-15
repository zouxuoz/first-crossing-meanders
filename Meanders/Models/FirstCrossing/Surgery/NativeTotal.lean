import Meanders.Models.FirstCrossing.Surgery.DrainTotal
import Meanders.Models.FirstCrossing.Native.Stage
import Meanders.Models.FirstCrossing.Native.PortBound
import Meanders.Models.FirstCrossing.Native.Geometry
import Meanders.Models.FirstCrossing.Surgery.PhysicalCyclic

/-! Exact native operation totality and reconstruction of output geometry. -/

namespace Meanders.FirstCrossing

/-- Every successful physical attachment has its exact per-group length balance. -/
theorem attachOwner_length {w out : Splice} {owner g : Group} {down : Bool} {cup : Nat}
    (h : attachOwner w owner down cup = some out) :
    (out.ports.get g).length + (if g = owner then 2 * down.toNat else 0) =
      (w.ports.get g).length + if g = owner then 1 else 0 := by
  cases down with
  | false =>
      simp only [attachOwner, Bool.false_eq_true, ite_false, Option.some.injEq] at h
      subst out
      simp only [Ports.get_set, Bool.toNat_false, Nat.mul_zero]
      split <;> simp_all
  | true =>
      unfold attachOwner at h
      simp only [ite_true] at h
      cases hr : (w.ports.get owner).reverse with
      | nil => simp [hr] at h
      | cons old older =>
        simp only [hr] at h
        have hp := spliceJoin_ports h
        have hl : (w.ports.get owner).length = older.length + 1 := by
          have hh := congrArg List.length hr
          simpa using hh
        rw [hp, Ports.get_set]
        split <;> simp_all

/-- Convert concrete cyclic coverage into the storage-order normalization contract. -/
theorem CyclicFrontier.flat {w : Splice} (h : CyclicFrontier w.mate w.ports.cyclic) :
    w.ports.flat.Nodup ∧ CoversLive w := by
  refine ⟨w.ports.cyclic_perm_flat.nodup_iff.mp h.nodup, ?_⟩
  intro i
  exact w.ports.cyclic_perm_flat.mem_iff.symm.trans (h.covers i)

/-- One actual successful drain has the exact deleted-head frontier. -/
theorem CyclicFrontier.drain_one {w out : Splice} {left right : Group}
    (h : CyclicFrontier w.mate w.ports.cyclic) (hd : left ≠ right)
    (hs : drain 1 left right w = some out) :
    CyclicFrontier out.mate out.ports.cyclic ∧ out.ports = w.ports.popHeads left right := by
  obtain ⟨x, xs, y, ys, hl, hr, hj⟩ := drain_one_success hs
  have hn := h.flat.1
  have hc := h.flat.2
  obtain ⟨a, hx⟩ := (hc x).mp ((Ports.mem_flat_iff _ _).mpr ⟨left, by simp [hl]⟩)
  obtain ⟨b, hy⟩ := (hc y).mp ((Ports.mem_flat_iff _ _).mpr ⟨right, by simp [hr]⟩)
  obtain ⟨hm, hLive, -, -, hp⟩ := spliceJoin_result
    (w := {w with ports := w.ports.popHeads left right}) h.pairing hx hy
      (Ports.heads_ne hn hd hl hr) hj
  refine ⟨⟨hm, ?_, ?_, ?_⟩, hp⟩
  · rw [hp, Ports.popHeads_cyclic hn hd hl hr]
    exact h.nodup.filter _
  · intro i
    rw [hp, Ports.popHeads_cyclic hn hd hl hr, hLive]
    simp [List.mem_filter, h.covers]
  · rw [drain_one_eq hl hr, hj] at hs
    simp only [Option.bind_some] at hs
    split at hs
    · assumption
    · contradiction

/-- Either possible FIFO count succeeds once both owner groups contain that many names. -/
theorem CyclicFrontier.drain_small_total {w : Splice} (h :
    CyclicFrontier w.mate w.ports.cyclic) (upper : Bool) {k : Nat} (hk : k ≤ 1)
    (hl : k ≤ (w.ports.get (Group.onSide upper .left)).length)
    (hr : k ≤ (w.ports.get (Group.onSide upper .right)).length) :
    ∃ out, drain k (Group.onSide upper .left) (Group.onSide upper .right) w = some out ∧
      CyclicFrontier out.mate out.ports.cyclic ∧
      ∀ g, (out.ports.get g).length +
          (if g = Group.onSide upper .left ∨ g = Group.onSide upper .right then k else 0) =
        (w.ports.get g).length := by
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · refine ⟨w, rfl, h, ?_⟩
    intro g
    split <;> omega
  · have hleft : w.ports.get (Group.onSide upper .left) ≠ [] := by
      intro he; simp [he] at hl
    have hright : w.ports.get (Group.onSide upper .right) ≠ [] := by
      intro he; simp [he] at hr
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hleft
    obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hright
    have hd : Group.onSide upper .left ≠ Group.onSide upper .right := by
      cases upper <;> decide
    obtain ⟨out, hout⟩ : ∃ out,
        drain 1 (Group.onSide upper .left) (Group.onSide upper .right) w = some out := by
      cases upper
      · exact drain_one_total_lower h.flat.1 h.pairing h.flat.2 h.check hx hy
      · exact drain_one_total_upper h.flat.1 h.pairing h.flat.2 h.check hx hy
    obtain ⟨hf, hp⟩ := h.drain_one hd hout
    refine ⟨out, hout, hf, ?_⟩
    intro g
    rw [hp, Ports.popHeads_get _ hd]
    by_cases hgl : g = Group.onSide upper .left
    · subst g
      simp [hx]
    by_cases hgr : g = Group.onSide upper .right
    · subst g
      simp [hy, hgl]
    simp [hgl, hgr]

/-- Original counter feasibility exposes its four independent group clauses. -/
theorem countersValid_group {s : RunSpec} {t : Stage} {c : Counters}
    (h : countersValid s t c = true) (g : Group) :
    t.processed g.side ≤ s.sideLength g.side ∧ 2 * c.get g ≤ t.processed g.side ∧
      c.get g ≤ s.budgets.get g ∧
      s.budgets.get g - c.get g ≤ s.sideLength g.side - t.processed g.side := by
  have hh := List.all_eq_true.mp h g (by cases g <;> simp [Group.all])
  exact of_decide_eq_true hh

/-- The retained reservoir cannot exceed the original active height. -/
theorem reservoir_le_height (s : RunSpec) (t : Stage) (c : Counters) (g : Group) :
    (geometry s t c).reservoir.get g ≤ t.processed g.side - 2 * c.get g := by
  cases hs : s.sector <;> simp only [geometry, hs, Counters.get_ofFn] <;> omega

/-- The actual feasibility guards preserve all original counter constraints. -/
theorem moveAllowed_countersValid {s : RunSpec} {t : Stage} {x : Key}
    {side : Side} {m : Move} (hc : countersValid s t x.counters = true)
    (hm : moveAllowed s t x side m = true) :
    countersValid s (t.next side) (moveCounters x.counters side m) = true := by
  simp only [moveAllowed, Bool.and_eq_true] at hm
  obtain ⟨⟨⟨⟨hup, hdown⟩, hside⟩, hbud⟩, -⟩ := hm
  have hp := of_decide_eq_true (List.all_eq_true.mp hbud
    (Group.onSide true side) (by simp))
  have hq := of_decide_eq_true (List.all_eq_true.mp hbud
    (Group.onSide false side) (by simp))
  have hs := of_decide_eq_true hside
  apply List.all_eq_true.mpr
  intro g _
  apply decide_eq_true
  have hold := countersValid_group hc g
  have hrp := reservoir_le_height s t x.counters (Group.onSide true side)
  have hrq := reservoir_le_height s t x.counters (Group.onSide false side)
  cases side <;> cases m <;> cases g <;>
    simp_all [Group.onSide, Group.side, Counters.get, Counters.set,
      moveCounters, Move.upperDown, Move.lowerDown, Stage.next, Stage.processed]
  all_goals omega

/-- The chronological prefix guard is checked on left visits and unchanged on right visits. -/
theorem moveAllowed_prefixAllowed {s : RunSpec} {t : Stage} {x : Key}
    {side : Side} {m : Move} (hp : prefixAllowed s t x.counters = true)
    (hm : moveAllowed s t x side m = true) :
    prefixAllowed s (t.next side) (moveCounters x.counters side m) = true := by
  cases side with
  | left =>
      simp only [moveAllowed, Bool.and_eq_true] at hm
      exact hm.2
  | right =>
      cases m <;> simpa [prefixAllowed, moveCounters, Stage.next,
        Group.onSide, Counters.get, Counters.set, Move.upperDown, Move.lowerDown] using hp

/-- Both physical owner edits have exactly the counter-prescribed length balance. -/
theorem physical_length_balance {initial upper out : Splice} {side : Side} {m : Move}
    {pc qc : Nat} (c : Counters)
    (hp : attachOwner initial (Group.onSide true side) m.upperDown pc = some upper)
    (hq : attachOwner upper (Group.onSide false side) m.lowerDown qc = some out) (g : Group) :
    (out.ports.get g).length + 2 * ((moveCounters c side m).get g - c.get g) =
      (initial.ports.get g).length + if side = g.side then 1 else 0 := by
  have hp' := attachOwner_length (g := g) hp
  have hq' := attachOwner_length (g := g) hq
  cases side <;> cases m <;> cases g <;>
    simp_all [Group.onSide, Group.side, Counters.get, Counters.set,
      moveCounters, Move.upperDown, Move.lowerDown]

/-- Exact length conservation supplies both concrete FIFO heads before their drains. -/
theorem fifo_geometry_total {w : Splice} (h : CyclicFrontier w.mate w.ports.cyclic)
    (len : Counters) {p q : Nat} (hp : p ≤ 1) (hq : q ≤ 1)
    (hlen : ∀ g, len.get g + (if g = .pl ∨ g = .pr then p else q) =
      (w.ports.get g).length) :
    ∃ upper out, drain p .pl .pr w = some upper ∧ drain q .ql .qr upper = some out ∧
      CyclicFrontier out.mate out.ports.cyclic ∧ out.ports.lengths = len := by
  obtain ⟨upper, hu, huf, hul⟩ := h.drain_small_total true hp
    (by have := hlen .pl; simpa [Group.onSide] using Nat.le_add_left p len.pl |>.trans_eq this)
    (by have := hlen .pr; simpa [Group.onSide] using Nat.le_add_left p len.pr |>.trans_eq this)
  have hql := hlen .ql
  have hqr := hlen .qr
  have huql := hul .ql
  have huqr := hul .qr
  simp only [Group.onSide, ite_true, Counters.get, ite_false,
    reduceCtorEq, or_self, Nat.add_zero] at hql hqr huql huqr
  obtain ⟨out, ho, hof, hol⟩ := huf.drain_small_total false hq
    (by change q ≤ (upper.ports.get .ql).length; omega)
    (by change q ≤ (upper.ports.get .qr).length; omega)
  refine ⟨upper, out, hu, ho, hof, ?_⟩
  have hf (g : Group) : (out.ports.get g).length = len.get g := by
    have ha := hlen g
    have hb := hul g
    have hc := hol g
    cases g <;> simp_all [Group.onSide, Counters.get] <;> omega
  cases len
  have hpl := hf .pl
  have hpr := hf .pr
  have hql := hf .ql
  have hqr := hf .qr
  simp only [Ports.get, Counters.get] at hpl hpr hql hqr
  simp [Ports.lengths, hpl, hpr, hql, hqr]

/-- A processed physical component has either a live endpoint or a recorded closure. -/
def BoundaryOrCycle (w : Splice) : Prop := 0 < w.cycles ∨ ∃ i, Live w.mate i

/-- A successful actual join either leaves its rewired mate live or records a cycle. -/
theorem spliceJoin_boundary {w out : Splice} {x y : Nat} (hm : MateInvariant w.mate)
    (h : spliceJoin w x y = some out) : MateInvariant out.mate ∧ BoundaryOrCycle out := by
  have hxy : x ≠ y := by intro he; subst y; simp [spliceJoin] at h
  have hx : ∃ a, HasMate w.mate x a := by
    cases hget : w.mate[x]? with
    | none => simp [spliceJoin, hget] at h
    | some value =>
      cases value with
      | none => simp [spliceJoin, hget] at h
      | some a => exact ⟨a, hget⟩
  obtain ⟨a, hx⟩ := hx
  have hy : ∃ b, HasMate w.mate y b := by
    have hxx := hx
    unfold HasMate at hxx
    cases hget : w.mate[y]? with
    | none => simp [spliceJoin, hxx, hget] at h
    | some value =>
      cases value with
      | none => simp [spliceJoin, hxx, hget] at h
      | some b => exact ⟨b, hget⟩
  obtain ⟨b, hy⟩ := hy
  obtain ⟨ho, hlive, hcycles, -, -⟩ := spliceJoin_result hm hx hy hxy h
  refine ⟨ho, ?_⟩
  by_cases hay : a = y
  · left
    simp [hay] at hcycles
    omega
  · right
    refine ⟨a, (hlive a).mpr ⟨⟨x, hm.symm hx⟩, ?_, hay⟩⟩
    exact (hm x a hx).1.symm

/-- Either physical owner operation preserves a live endpoint or a recorded closure. -/
theorem attachOwner_boundary {w out : Splice} {g : Group} {down : Bool} {cup : Nat}
    (hm : MateInvariant w.mate) (hb : BoundaryOrCycle w)
    (h : attachOwner w g down cup = some out) :
    MateInvariant out.mate ∧ BoundaryOrCycle out := by
  cases down with
  | false =>
      simp only [attachOwner, Bool.false_eq_true, ite_false, Option.some.injEq] at h
      subst out
      exact ⟨hm, hb⟩
  | true =>
      unfold attachOwner at h
      simp only [ite_true] at h
      cases hr : (w.ports.get g).reverse with
      | nil => simp [hr] at h
      | cons old older =>
        simp only [hr] at h
        exact spliceJoin_boundary (w := {w with ports := w.ports.set g older.reverse}) hm h

/-- Every successful drain retains a live endpoint or a recorded closure. -/
theorem drain_boundary {k : Nat} {left right : Group} {w out : Splice}
    (hm : MateInvariant w.mate) (hb : BoundaryOrCycle w)
    (h : drain k left right w = some out) : MateInvariant out.mate ∧ BoundaryOrCycle out := by
  induction k generalizing w with
  | zero => cases h; exact ⟨hm, hb⟩
  | succ k ih =>
      cases hl : w.ports.get left with
      | nil => simp [drain, hl] at h
      | cons x xs =>
        cases hr : w.ports.get right with
        | nil => simp [drain, hl, hr] at h
        | cons y ys =>
          simp only [drain, hl, hr, List.head?_cons, List.tail_cons,
            Option.bind_eq_bind, Option.bind_some] at h
          cases hj : spliceJoin
              {w with ports := (w.ports.set left xs).set right ys} x y with
          | none => simp [hj] at h
          | some z =>
              simp only [hj, Option.bind_some] at h
              split at h
              · simp at h
              · have hz := spliceJoin_boundary
                  (w := {w with ports := (w.ports.set left xs).set right ys}) hm hj
                exact ih hz.1 hz.2 h

/-- The existing native closure guard, separated from structural operation totality. -/
def CycleAccepted (s : RunSpec) (t : Stage) (w : Splice) : Prop :=
  w.cycles = 0 ∨ (w.cycles = 1 ∧ t.tick = 2 * s.n ∧ w.ports.flat = [])

instance (s : RunSpec) (t : Stage) (w : Splice) : Decidable (CycleAccepted s t w) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Exact native surgery is total before its explicit final cycle-acceptance decision. -/
theorem candidateSplice_stages {s : RunSpec} {t : Stage} {x : Key}
    {side : Side} {m : Move} (hx : validKey s t x = true)
    (hm : moveAllowed s t x side m = true) :
    let old := geometry s t x.counters
    let new := geometry s (t.next side) (moveCounters x.counters side m)
    let initial : Splice := ⟨Ports.ofLengths old.length,
      x.mate.map some ++ [some (x.mate.length + 1), some x.mate.length], 0⟩
    ∃ upper attached pdrained out,
      attachOwner initial (Group.onSide true side) m.upperDown x.mate.length = some upper ∧
      attachOwner upper (Group.onSide false side) m.lowerDown (x.mate.length + 1) = some attached ∧
      drain (min new.emitted.pl new.emitted.pr - min old.emitted.pl old.emitted.pr)
        .pl .pr attached = some pdrained ∧
      drain (min new.emitted.ql new.emitted.qr - min old.emitted.ql old.emitted.qr)
        .ql .qr pdrained = some out ∧
      CyclicFrontier out.mate out.ports.cyclic ∧
      out.ports.lengths = (geometry s (t.next side) (moveCounters x.counters side m)).length ∧
      BoundaryOrCycle out ∧ candidateSplice s t x side m =
        if CycleAccepted s (t.next side) out then some out else none := by
  dsimp only
  have hguards := hx
  simp only [validKey, Bool.and_eq_true] at hguards
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hc⟩, -⟩, -⟩, -⟩, -⟩ := hguards
  have hcnew := moveAllowed_countersValid hc hm
  have hbudget g := (countersValid_group hc g).2.2.1
  have hbudgetNew g := (countersValid_group hcnew g).2.2.1
  let old := geometry s t x.counters
  let new := geometry s (t.next side) (moveCounters x.counters side m)
  let p := min new.emitted.pl new.emitted.pr - min old.emitted.pl old.emitted.pr
  let q := min new.emitted.ql new.emitted.qr - min old.emitted.ql old.emitted.qr
  have hjp := joined_next_between s t x.counters side m .pl hbudget hbudgetNew
  have hjq := joined_next_between s t x.counters side m .ql hbudget hbudgetNew
  change min old.emitted.pl old.emitted.pr ≤ min new.emitted.pl new.emitted.pr ∧ p ≤ 1 at hjp
  change min old.emitted.ql old.emitted.qr ≤ min new.emitted.ql new.emitted.qr ∧ q ≤ 1 at hjq
  let initial : Splice := ⟨Ports.ofLengths old.length,
    x.mate.map some ++ [some (x.mate.length + 1), some x.mate.length], 0⟩
  obtain ⟨upper, physical, hup, hphysical, hf⟩ := candidate_physical_cyclic_total hx hm
  change attachOwner initial _ _ _ = some upper at hup
  have hi : MateInvariant initial.mate := by
    simpa only [initial, List.length_map] using
      appendCup_invariant (validKey_cyclicFrontier hx).pairing
  have hib : BoundaryOrCycle initial := by
    right
    refine ⟨x.mate.length, ?_⟩
    simpa only [initial, List.length_map] using
      (appendCup_live (x.mate.map some) (x.mate.map some).length).mpr (Or.inr (Or.inl rfl))
  have hub := attachOwner_boundary hi hib hup
  have hpb := attachOwner_boundary hub.1 hub.2 hphysical
  have hlen (g : Group) : new.length.get g + (if g = .pl ∨ g = .pr then p else q) =
      (physical.ports.get g).length := by
    have ha := geometry_length_next_conservation s t x.counters side m g
      (countersValid_group hc g).2.1 (countersValid_group hcnew g).2.1 hbudget hbudgetNew
    have hb := physical_length_balance x.counters hup hphysical g
    have hi : (initial.ports.get g).length = old.length.get g := by
      cases g <;> simp [initial, Ports.ofLengths, Ports.get, Counters.get]
    rw [hi] at hb
    change new.length.get g +
      (min (new.emitted.get g) (new.emitted.get g.other) -
        min (old.emitted.get g) (old.emitted.get g.other)) +
      2 * ((moveCounters x.counters side m).get g - x.counters.get g) =
        old.length.get g + if side = g.side then 1 else 0 at ha
    cases g <;> simp only [Counters.get, Group.other, reduceCtorEq, true_or,
      or_true, or_self, ite_true, ite_false, Nat.min_comm] at ha hb ⊢ <;> omega
  obtain ⟨pout, out, hpout, hout, hof, hol⟩ := fifo_geometry_total hf new.length hjp.2 hjq.2 hlen
  have hpub := drain_boundary hpb.1 hpb.2 hpout
  have hob := drain_boundary hpub.1 hpub.2 hout
  refine ⟨upper, physical, pout, out, hup, hphysical, hpout, hout, hof, hol, hob.2, ?_⟩
  have hoperation : candidateSplice s t x side m =
      if 0 < out.cycles then
        if !(decide (out.cycles = 1 ∧ (t.next side).tick = 2 * s.n ∧ out.ports.flat = []))
          then none else some out
      else some out := by
    cases hs : s.sector with
    | low =>
      have hpeq : p = 0 := by simp [p, new, old, geometry, hs, Counters.zero]
      have hqeq : q = 0 := by simp [q, new, old, geometry, hs, Counters.zero]
      simp only [hpeq, drain_zero, Option.some.injEq] at hpout
      simp only [hqeq, drain_zero, Option.some.injEq] at hout
      subst pout out
      dsimp only [initial, old] at hup
      simp [candidateSplice, hm, hup, hphysical, hf.check, hs]
    | high L u v =>
      have hbackP : ¬ min new.emitted.pl new.emitted.pr <
          min old.emitted.pl old.emitted.pr := by omega
      have hbackQ : ¬ min new.emitted.ql new.emitted.qr <
          min old.emitted.ql old.emitted.qr := by omega
      dsimp only [initial, old] at hup
      have hself (c : Counters) : (c != c) = false := by
        cases c
        simp [bne, BEq.beq, instBEqCounters.beq]
      dsimp only [p, q, new, old] at hbackP hbackQ hpout hout hol
      simp [candidateSplice, hm, hup, hphysical, hf.check, hs,
        hbackP, hbackQ, hpout, hout, hol, hself]
  rw [hoperation]
  unfold CycleAccepted
  by_cases hz : out.cycles = 0
  · simp [hz]
  · have hp : 0 < out.cycles := by omega
    simp only [hp, ite_true, hz, false_or, Bool.not_eq_true',
      decide_eq_false_iff_not, ite_not]

/-- Exact native surgery is total before its explicit final cycle-acceptance decision. -/
theorem candidateSplice_total_before_cycles {s : RunSpec} {t : Stage} {x : Key}
    {side : Side} {m : Move} (hx : validKey s t x = true)
    (hm : moveAllowed s t x side m = true) :
    ∃ out, CyclicFrontier out.mate out.ports.cyclic ∧
      out.ports.lengths = (geometry s (t.next side) (moveCounters x.counters side m)).length ∧
      BoundaryOrCycle out ∧ candidateSplice s t x side m =
        if CycleAccepted s (t.next side) out then some out else none := by
  obtain ⟨upper, attached, pdrained, out, -, -, -, -, hf, hl, hb, he⟩ :=
    candidateSplice_stages hx hm
  exact ⟨out, hf, hl, hb, he⟩

/-- Storage reconstruction preserves the exact total number of retained endpoints. -/
theorem Ports.flat_length_ofLengths (p : Ports) :
    (Ports.ofLengths p.lengths).flat.length = p.flat.length := by
  simp [Ports.flat, Ports.lengths, Ports.ofLengths, Nat.add_assoc]

/-- Canonical normalization passes all raw-key guards once the explicit cycle rule accepts. -/
theorem normalize_validKey {s : RunSpec} {t : Stage} {c : Counters} {w : Splice} {y : Key}
    (hs : s.valid = true) (ht : t.valid s = true)
    (hc : countersValid s t c = true) (hp : prefixAllowed s t c = true)
    (hf : CyclicFrontier w.mate w.ports.cyclic)
    (hl : w.ports.lengths = (geometry s t c).length)
    (hb : BoundaryOrCycle w) (ha : CycleAccepted s t w)
    (hn : normalize c w = some y) : validKey s t y = true := by
  have hyc := normalize_counters hn
  have hlen : y.mate.length = (Ports.ofLengths (geometry s t y.counters).length).flat.length := by
    rw [hyc, ← hl, Ports.flat_length_ofLengths]
    exact normalize_length hn
  have hcounter : countersValid s t y.counters = true := hyc ▸ hc
  have hprefix : prefixAllowed s t y.counters = true := hyc ▸ hp
  have hbound := mate_length_port_bound s t y hs ht hcounter hprefix hlen
  have hempty (he : y.mate = []) : t.tick = 0 ∨ t.tick = 2 * s.n := by
    have hw : w.ports.flat = [] := List.length_eq_zero_iff.mp (by
      have hh := normalize_length hn
      rw [he, List.length_nil] at hh
      omega)
    have hpos : 0 < w.cycles := by
      rcases hb with hb | ⟨i, hi⟩
      · exact hb
      · have hmem := (hf.flat.2 i).mpr hi
        simp [hw] at hmem
    rcases ha with ha | ha
    · omega
    · exact Or.inr ha.2.1
  have hpair := normalize_pairingValid hn hf.flat.1 hf.pairing hf.flat.2
  have hcyc := normalize_cyclicCheck hf hn
  rw [hl, ← hyc] at hcyc
  simp only [validKey, hs, ht, hcounter, hprefix, hpair, hcyc,
    Bool.true_and, Bool.and_true]
  exact decide_eq_true ⟨hlen, hbound, hempty⟩

/-- The actual candidate, including normalization and every output structural guard,
is total precisely up to its original cycle-acceptance predicate. -/
theorem candidate_total_before_cycles {s : RunSpec} {t : Stage} {x : Key}
    {side : Side} {m : Move} (hx : validKey s t x = true)
    (hm : moveAllowed s t x side m = true) (hside : s.schedule[t.tick]? = some side) :
    ∃ w y, CyclicFrontier w.mate w.ports.cyclic ∧
      normalize (moveCounters x.counters side m) w = some y ∧
      (CycleAccepted s (t.next side) w → validKey s (t.next side) y = true) ∧
      candidate s t x side m = if CycleAccepted s (t.next side) w then some y else none := by
  obtain ⟨w, hf, hl, hb, hw⟩ := candidateSplice_total_before_cycles hx hm
  obtain ⟨y, hy⟩ := normalize_total hf.flat.1 hf.pairing hf.flat.2
    (moveCounters x.counters side m)
  refine ⟨w, y, hf, hy, ?_, ?_⟩
  · intro ha
    have hg := hx
    simp only [validKey, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨⟨hs, ht⟩, hc⟩, hp⟩, -⟩, -⟩, -⟩ := hg
    exact normalize_validKey hs (Stage.valid_next hs ht hside)
      (moveAllowed_countersValid hc hm) (moveAllowed_prefixAllowed hp hm) hf hl hb ha hy
  · unfold candidate
    rw [hw]
    split <;> simp_all

/-- Raw successor validation adds no rejection beyond the specified cycle rule. -/
theorem rawStep_total_before_cycles {s : RunSpec} {t : Stage} {x : Key}
    {side : Side} {m : Move} (hx : validKey s t x = true)
    (hm : moveAllowed s t x side m = true) (hside : s.schedule[t.tick]? = some side) :
    ∃ w y, CyclicFrontier w.mate w.ports.cyclic ∧
      normalize (moveCounters x.counters side m) w = some y ∧
      rawStep s t x m = if CycleAccepted s (t.next side) w then some y else none := by
  obtain ⟨w, y, hf, hn, hv, he⟩ := candidate_total_before_cycles hx hm hside
  refine ⟨w, y, hf, hn, ?_⟩
  by_cases ha : CycleAccepted s (t.next side) w
  · simp [rawStep, hx, hside, he, ha, hv ha]
  · simp [rawStep, hx, hside, he, ha]


end Meanders.FirstCrossing
