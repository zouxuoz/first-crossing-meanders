import Meanders.Models.FirstCrossing.Surgery.CyclicSplice
import Meanders.Models.FirstCrossing.Surgery.Cup
import Meanders.Models.FirstCrossing.Native.State

/-!
# Exact port-list updates at a physical crossing

These are list identities for the native `Ports.set` operations. They do not
assert noncrossing: they identify the adjacent endpoints to which the geometric
surgery lemmas apply.
-/

namespace Meanders.FirstCrossing

/-- Reading a recorded group length is the length of that same physical list. -/
theorem Ports.lengths_get (p : Ports) (g : Group) :
    p.lengths.get g = (p.get g).length := by
  cases g <;> rfl

/-- A positive reservoir always occupies retained ports, including the LOW sector. -/
theorem reservoir_le_retained_length (s : RunSpec) (t : Stage) (c : Counters)
    (g : Group) : (geometry s t c).reservoir.get g ≤ (geometry s t c).length.get g := by
  cases hs : s.sector with
  | low => simp [geometry, hs]
  | high L u v => simp only [geometry, hs, Counters.get_ofFn]; omega

/-- The executable down-step guard supplies an actual newest retained endpoint. -/
theorem Ports.exists_newest_of_reservoir_pos {s : RunSpec} {t : Stage} {c : Counters}
    {p : Ports} {g : Group} (hp : p.lengths = (geometry s t c).length)
    (hr : 0 < (geometry s t c).reservoir.get g) :
    ∃ (older : List Nat) (old : Nat), p.get g = older ++ [old] := by
  have hlen : 0 < (p.get g).length := by
    rw [← Ports.lengths_get, hp]
    exact lt_of_lt_of_le hr (reservoir_le_retained_length s t c g)
  cases he : (p.get g).reverse with
  | nil => have : p.get g = [] := by simpa using congrArg List.reverse he
           simp [this] at hlen
  | cons old revOlder =>
    refine ⟨revOlder.reverse, old, ?_⟩
    simpa using congrArg List.reverse he

/-- The cyclic frontier immediately after introducing both physical cup endpoints. -/
def bothCupOrder (p : Ports) (side : Side) (pc qc : Nat) : List Nat :=
  match side with
  | .left => [pc] ++ p.cyclic ++ [qc]
  | .right => p.pl.reverse ++ p.pr ++ [pc, qc] ++ p.qr.reverse ++ p.ql

/-- The cyclic frontier after the upper attachment, with the lower cup pending. -/
def lowerCupOrder (p : Ports) (side : Side) (qc : Nat) : List Nat :=
  match side with
  | .left => p.cyclic ++ [qc]
  | .right => p.pl.reverse ++ p.pr ++ [qc] ++ p.qr.reverse ++ p.ql

/-- Extending the upper reservoir places its cup at the existing physical seam. -/
theorem upper_up_order (p : Ports) (side : Side) (pc qc : Nat) :
    lowerCupOrder (p.set (Group.onSide true side)
      (p.get (Group.onSide true side) ++ [pc])) side qc = bothCupOrder p side pc qc := by
  cases side <;>
    simp [bothCupOrder, lowerCupOrder, Ports.set, Ports.get, Ports.cyclic,
      Group.onSide, List.append_assoc]

/-- Extending the lower reservoir consumes the last pending cup name. -/
theorem lower_up_order (p : Ports) (side : Side) (qc : Nat) :
    (p.set (Group.onSide false side)
      (p.get (Group.onSide false side) ++ [qc])).cyclic = lowerCupOrder p side qc := by
  cases side <;>
    simp [lowerCupOrder, Ports.set, Ports.get, Ports.cyclic, Group.onSide, List.append_assoc]

/-- A down upper attachment deletes an adjacent cup/newest-port pair in the
actual cyclic order; the direction reverses between the two physical sides. -/
theorem upper_down_order_split (p : Ports) (side : Side) (pc qc old : Nat)
    (older : List Nat) (htop : p.get (Group.onSide true side) = older ++ [old]) :
    ∃ before after,
      (bothCupOrder p side pc qc = before ++ [old, pc] ++ after ∨
        bothCupOrder p side pc qc = before ++ [pc, old] ++ after) ∧
      lowerCupOrder (p.set (Group.onSide true side) older) side qc = before ++ after := by
  cases side with
  | left =>
    refine ⟨[], older.reverse ++ p.pr ++ p.qr.reverse ++ p.ql ++ [qc], Or.inr ?_, ?_⟩ <;>
      simp_all [bothCupOrder, lowerCupOrder, Ports.set, Ports.get, Ports.cyclic,
        Group.onSide, List.append_assoc]
  | right =>
    refine ⟨p.pl.reverse ++ older, [qc] ++ p.qr.reverse ++ p.ql, Or.inl ?_, ?_⟩ <;>
      simp_all [bothCupOrder, lowerCupOrder, Ports.set, Ports.get,
        Group.onSide, List.append_assoc]

/-- The pending lower cup and newest lower port are adjacent, with the actual
post-attachment cyclic list obtained by deleting just these two names. -/
theorem lower_down_order_split (p : Ports) (side : Side) (qc old : Nat)
    (older : List Nat) (htop : p.get (Group.onSide false side) = older ++ [old]) :
    ∃ before after,
      (lowerCupOrder p side qc = before ++ [old, qc] ++ after ∨
        lowerCupOrder p side qc = before ++ [qc, old] ++ after) ∧
      (p.set (Group.onSide false side) older).cyclic = before ++ after := by
  cases side with
  | left =>
    refine ⟨p.pl.reverse ++ p.pr ++ p.qr.reverse ++ older, [], Or.inl ?_, ?_⟩ <;>
      simp_all [lowerCupOrder, Ports.set, Ports.get, Ports.cyclic,
        Group.onSide, List.append_assoc]
  | right =>
    refine ⟨p.pl.reverse ++ p.pr, older.reverse ++ p.ql, Or.inr ?_, ?_⟩ <;>
      simp_all [lowerCupOrder, Ports.set, Ports.get, Ports.cyclic,
        Group.onSide, List.append_assoc]

/-- The new physical endpoints both occur in the augmented frontier. -/
theorem mem_bothCupOrder (p : Ports) (side : Side) (pc qc : Nat) :
    pc ∈ bothCupOrder p side pc qc ∧ qc ∈ bothCupOrder p side pc qc := by
  cases side <;> simp [bothCupOrder]

/-- Original upper ports remain listed until their physical attachment. -/
theorem upper_mem_bothCupOrder (p : Ports) (side : Side) (pc qc x : Nat)
    (hx : x ∈ p.get (Group.onSide true side)) : x ∈ bothCupOrder p side pc qc := by
  cases side <;> simp_all [bothCupOrder, Ports.cyclic, Group.onSide, Ports.get]

/-- The lower cup remains listed after the upper attachment. -/
theorem mem_lowerCupOrder (p : Ports) (side : Side) (qc : Nat) :
    qc ∈ lowerCupOrder p side qc := by
  cases side <;> simp [lowerCupOrder]

/-- Original lower ports remain listed until their physical attachment. -/
theorem lower_mem_lowerCupOrder (p : Ports) (side : Side) (qc x : Nat)
    (hx : x ∈ p.get (Group.onSide false side)) : x ∈ lowerCupOrder p side qc := by
  cases side <;> simp_all [lowerCupOrder, Ports.cyclic, Group.onSide, Ports.get]

/-- An upper attachment leaves the lower owner's original list unchanged. -/
theorem upper_set_lower_get (p : Ports) (side : Side) (upper : List Nat) :
    (p.set (Group.onSide true side) upper).get (Group.onSide false side) =
      p.get (Group.onSide false side) := by
  cases side <;> rfl

end Meanders.FirstCrossing

/-!
# Physical cup and owner-step planarity

The actual candidate array is extended by its fresh two-incidence cup.
Augmented cyclic orders retain cups that have not yet been attached to their
owner groups. Each executable attachment preserves the exact live planar pairing.
-/

namespace Meanders.FirstCrossing

/-- The temporary array and a cyclic order describe exactly one planar live frontier. -/
structure CyclicFrontier (mate : List (Option Nat)) (names : List Nat) : Prop where
  /-- Every live endpoint has its distinct reverse mate. -/
  pairing : MateInvariant mate
  /-- Every endpoint appears once in cyclic order. -/
  nodup : names.Nodup
  /-- Consumed array holes are omitted, and no live endpoint is omitted. -/
  covers : ∀ i, i ∈ names ↔ Live mate i
  /-- The native stack check accepts this exact cyclic order. -/
  check : cyclicCheck mate names [] = true

/-- A scan depends only on the mate lookups at the physical names it reads. -/
theorem cyclicCheck_congr_on (a b : List (Option Nat)) (names stack : List Nat)
    (h : ∀ i ∈ names, a[i]? = b[i]?) :
    cyclicCheck a names stack = cyclicCheck b names stack := by
  induction names generalizing stack with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (List.mem_cons_self ..)
      have ht := ih (h := fun i hi => h i (List.mem_cons_of_mem _ hi))
      cases stack with
      | nil =>
          simp only [cyclicCheck, hx]
          cases hb : b[x]?.join <;> simp only [ht]
      | cons y ys =>
          simp only [cyclicCheck, hx]
          by_cases he : (x == y) = true
          · simp only [he, ite_true, ht]
          · simp only [he]
            cases hb : b[x]?.join <;> simp only [ht]

/-- A fresh adjacent cup is read as an immediate push/pop, leaving the old scan unchanged. -/
theorem appendCup_cyclicCheck_front {mate : List (Option Nat)} {names : List Nat}
    (hb : ∀ i ∈ names, i < mate.length) (hc : cyclicCheck mate names [] = true) :
    cyclicCheck (mate ++ [some (mate.length + 1), some mate.length])
      (mate.length :: (mate.length + 1) :: names) [] = true := by
  have h0 : (mate ++ [some (mate.length + 1), some mate.length])[mate.length]?.join =
      some (mate.length + 1) := by simp
  simp only [cyclicCheck, h0, beq_self_eq_true, ite_true]
  rw [cyclicCheck_congr_on _ mate names [] (fun i hi => List.getElem?_append_left (hb i hi))]
  exact hc

/-- The cup may be encountered in the reverse cyclic orientation as well. -/
theorem appendCup_cyclicCheck_front_reverse {mate : List (Option Nat)} {names : List Nat}
    (hb : ∀ i ∈ names, i < mate.length) (hc : cyclicCheck mate names [] = true) :
    cyclicCheck (mate ++ [some (mate.length + 1), some mate.length])
      ((mate.length + 1) :: mate.length :: names) [] = true := by
  have h1 : (mate ++ [some (mate.length + 1), some mate.length])[mate.length + 1]?.join =
      some mate.length := by simp
  simp only [cyclicCheck, h1, beq_self_eq_true, ite_true]
  rw [cyclicCheck_congr_on _ mate names [] (fun i hi => List.getElem?_append_left (hb i hi))]
  exact hc

/-- A listed old name is strictly below the fresh candidate offsets. -/
theorem CyclicFrontier.name_bound {mate : List (Option Nat)} {names : List Nat}
    (h : CyclicFrontier mate names) {i : Nat} (hi : i ∈ names) : i < mate.length := by
  obtain ⟨j, hij⟩ := (h.covers i).mp hi
  exact hij.bound

/-- Cup creation preserves all four temporary-frontier clauses at its first seam. -/
theorem CyclicFrontier.appendCup_front {mate : List (Option Nat)} {names : List Nat}
    (h : CyclicFrontier mate names) :
    CyclicFrontier (mate ++ [some (mate.length + 1), some mate.length])
      (mate.length :: (mate.length + 1) :: names) := by
  have h0 : mate.length ∉ names := fun hi => Nat.lt_irrefl _ (h.name_bound hi)
  have h1 : mate.length + 1 ∉ names := by intro hi; have := h.name_bound hi; omega
  refine ⟨appendCup_invariant h.pairing, ?_, ?_, appendCup_cyclicCheck_front
    (fun i hi => h.name_bound hi) h.check⟩
  · simp [List.nodup_cons, h0, h1, h.nodup]
  · intro i
    rw [appendCup_live, ← h.covers]
    simp only [List.mem_cons]
    tauto

/-- A cyclic rotation retains the same exact live pairing. -/
theorem CyclicFrontier.swap_blocks {mate : List (Option Nat)} {before after : List Nat}
    (h : CyclicFrontier mate (before ++ after)) : CyclicFrontier mate (after ++ before) := by
  refine ⟨h.pairing, List.perm_append_comm.nodup_iff.mp h.nodup, ?_,
    (cyclicCheck_swap_blocks_iff h.nodup h.pairing h.covers).mp h.check⟩
  intro i
  simpa only [List.mem_append, or_comm] using h.covers i

/-- The exact fresh cup can be inserted at any interior seam of the old cyclic list. -/
theorem CyclicFrontier.appendCup_blocks {mate : List (Option Nat)}
    {before after : List Nat} (h : CyclicFrontier mate (before ++ after)) :
    CyclicFrontier (mate ++ [some (mate.length + 1), some mate.length])
      (before ++ [mate.length, mate.length + 1] ++ after) := by
  have hc := h.swap_blocks.appendCup_front
  have hc' : CyclicFrontier (mate ++ [some (mate.length + 1), some mate.length])
      (([mate.length, mate.length + 1] ++ after) ++ before) := by
    simpa only [List.cons_append, List.nil_append, List.append_assoc] using hc
  simpa only [List.append_assoc] using hc'.swap_blocks

/-- Reversing only the newly inserted cup pair retains the same array and frontier. -/
theorem CyclicFrontier.appendCup_front_reverse {mate : List (Option Nat)} {names : List Nat}
    (h : CyclicFrontier mate names) :
    CyclicFrontier (mate ++ [some (mate.length + 1), some mate.length])
      ((mate.length + 1) :: mate.length :: names) := by
  have h0 : mate.length ∉ names := fun hi => Nat.lt_irrefl _ (h.name_bound hi)
  have h1 : mate.length + 1 ∉ names := by intro hi; have := h.name_bound hi; omega
  refine ⟨appendCup_invariant h.pairing, ?_, ?_, appendCup_cyclicCheck_front_reverse
    (fun i hi => h.name_bound hi) h.check⟩
  · simp [List.nodup_cons, h0, h1, h.nodup]
  · intro i
    rw [appendCup_live, ← h.covers]
    simp only [List.mem_cons]
    tauto

/-- The left physical cup straddles the chosen start of cyclic order. -/
theorem CyclicFrontier.appendCup_wrap {mate : List (Option Nat)} {names : List Nat}
    (h : CyclicFrontier mate names) :
    CyclicFrontier (mate ++ [some (mate.length + 1), some mate.length])
      ([mate.length] ++ names ++ [mate.length + 1]) := by
  have hc : CyclicFrontier (mate ++ [some (mate.length + 1), some mate.length])
      ([mate.length + 1] ++ (mate.length :: names)) := h.appendCup_front_reverse
  simpa only [List.cons_append, List.nil_append] using hc.swap_blocks

/-- Cup creation gives the prescribed augmented order on either physical side. -/
theorem CyclicFrontier.appendCup_physical {mate : List (Option Nat)} {p : Ports}
    (h : CyclicFrontier mate p.cyclic) (side : Side) :
    CyclicFrontier (mate ++ [some (mate.length + 1), some mate.length])
      (bothCupOrder p side mate.length (mate.length + 1)) := by
  cases side with
  | left => exact h.appendCup_wrap
  | right =>
      have hh : CyclicFrontier mate ((p.pl.reverse ++ p.pr) ++ (p.qr.reverse ++ p.ql)) := by
        simpa only [Ports.cyclic, List.append_assoc] using h
      simpa only [bothCupOrder, List.append_assoc] using hh.appendCup_blocks

/-- An actual adjacent native join preserves all temporary-frontier clauses. -/
theorem CyclicFrontier.splice_adjacent {w out : Splice} {names : List Nat} {x y : Nat}
    (h : CyclicFrontier w.mate names) (hs : AtSeam names x y ∨ AtSeam names y x)
    (hj : spliceJoin w x y = some out) :
    CyclicFrontier out.mate (names.filter (fun i => i != x && i != y)) := by
  have hmem : x ∈ names ∧ y ∈ names := by
    rcases hs with hs | hs
    · exact hs.members
    · exact hs.members.symm
  obtain ⟨a, hx⟩ := (h.covers x).mp hmem.1
  obtain ⟨b, hy⟩ := (h.covers y).mp hmem.2
  have hxy : x ≠ y := by intro he; subst y; simp [spliceJoin] at hj
  have hout := spliceJoin_result h.pairing hx hy hxy hj
  refine ⟨hout.1, h.nodup.filter _, ?_,
    spliceJoin_cyclicCheck_adjacent h.nodup h.pairing h.covers h.check hs hj⟩
  intro i
  rw [hout.2.1 i]
  simp [List.mem_filter, h.covers]

/-- The block form identifies the exact post-join order in either seam orientation. -/
theorem CyclicFrontier.splice_blocks {w out : Splice} {names : List Nat} {x y : Nat}
    {before after : List Nat} (h : CyclicFrontier w.mate names)
    (hs : names = before ++ [x, y] ++ after ∨ names = before ++ [y, x] ++ after)
    (hj : spliceJoin w x y = some out) : CyclicFrontier out.mate (before ++ after) := by
  have hseam : AtSeam names x y ∨ AtSeam names y x := by
    rcases hs with hs | hs
    · exact Or.inl (Or.inl ⟨before, after, hs⟩)
    · exact Or.inr (Or.inl ⟨before, after, hs⟩)
  have hout := h.splice_adjacent hseam hj
  rcases hs with rfl | rfl
  · rwa [filter_remove_blocks h.nodup] at hout
  · have he : (before ++ [y, x] ++ after).filter (fun i => i != x && i != y) =
        before ++ after := by
      simpa only [Bool.and_comm] using filter_remove_blocks h.nodup
    rwa [he] at hout

/-- Distinct covered adjacent endpoints cannot fail any native splice guard. -/
theorem CyclicFrontier.splice_blocks_total {w : Splice} {names : List Nat} {x y : Nat}
    {before after : List Nat} (h : CyclicFrontier w.mate names)
    (hs : names = before ++ [x, y] ++ after ∨ names = before ++ [y, x] ++ after) :
    ∃ out, spliceJoin w x y = some out ∧ CyclicFrontier out.mate (before ++ after) ∧
      out.ports = w.ports := by
  have hmem : x ∈ names ∧ y ∈ names := by
    rcases hs with hs | hs <;> simp [hs]
  have hxy : x ≠ y := by
    rcases hs with hs | hs
    · have hn := h.nodup
      rw [hs] at hn
      have hp := (List.nodup_append.mp (List.nodup_append.mp hn).1).2.1
      simpa using hp
    · have hn := h.nodup
      rw [hs] at hn
      have hp := (List.nodup_append.mp (List.nodup_append.mp hn).1).2.1
      simpa [ne_comm] using hp
  obtain ⟨a, hx⟩ := (h.covers x).mp hmem.1
  obtain ⟨b, hy⟩ := (h.covers y).mp hmem.2
  obtain ⟨out, hout, -, -, -, -, hp⟩ := spliceJoin_spec h.pairing hx hy hxy
  exact ⟨out, hout, h.splice_blocks hs hout, hp⟩

private theorem exists_newest {names : List Nat} (hne : names ≠ []) :
    ∃ older old, names = older ++ [old] := by
  obtain ⟨old, revOlder, he⟩ := List.ne_nil_iff_exists_cons.mp
    (show names.reverse ≠ [] by
      intro he
      apply hne
      simpa using congrArg List.reverse he)
  exact ⟨revOlder.reverse, old, by simpa using congrArg List.reverse he⟩

/-- The actual upper attachment succeeds and preserves the augmented cyclic
frontier, leaving the lower owner list unchanged. -/
theorem upper_attach_cyclic_total (w : Splice) (side : Side) (down : Bool) (pc qc : Nat)
    (h : CyclicFrontier w.mate (bothCupOrder w.ports side pc qc))
    (hd : down = true → w.ports.get (Group.onSide true side) ≠ []) :
    ∃ out, attachOwner w (Group.onSide true side) down pc = some out ∧
      CyclicFrontier out.mate (lowerCupOrder out.ports side qc) ∧
      out.ports.get (Group.onSide false side) = w.ports.get (Group.onSide false side) := by
  cases down with
  | false =>
      let updated := w.ports.set (Group.onSide true side)
        (w.ports.get (Group.onSide true side) ++ [pc])
      refine ⟨{w with ports := updated}, rfl, ?_, ?_⟩
      · dsimp only [updated]
        rw [upper_up_order]
        exact h
      · dsimp only [updated]
        exact upper_set_lower_get _ _ _
  | true =>
      obtain ⟨older, old, htop⟩ := exists_newest (hd rfl)
      obtain ⟨before, after, hsplit, hnew⟩ :=
        upper_down_order_split w.ports side pc qc old older htop
      let start : Splice := {w with ports := w.ports.set (Group.onSide true side) older}
      obtain ⟨out, hout, hfront, hports⟩ := CyclicFrontier.splice_blocks_total (w := start) h hsplit
      refine ⟨out, ?_, ?_, ?_⟩
      · rw [attachOwner_down_eq w _ pc old older htop]
        exact hout
      · rw [hports]
        change CyclicFrontier out.mate
          (lowerCupOrder (w.ports.set (Group.onSide true side) older) side qc)
        rw [hnew]
        exact hfront
      · rw [hports]
        exact upper_set_lower_get _ _ _

/-- The actual lower attachment consumes the last pending cup, yielding the
native output `ports.cyclic` with no external postcheck assumption. -/
theorem lower_attach_cyclic_total (w : Splice) (side : Side) (down : Bool) (qc : Nat)
    (h : CyclicFrontier w.mate (lowerCupOrder w.ports side qc))
    (hd : down = true → w.ports.get (Group.onSide false side) ≠ []) :
    ∃ out, attachOwner w (Group.onSide false side) down qc = some out ∧
      CyclicFrontier out.mate out.ports.cyclic := by
  cases down with
  | false =>
      let updated := w.ports.set (Group.onSide false side)
        (w.ports.get (Group.onSide false side) ++ [qc])
      refine ⟨{w with ports := updated}, rfl, ?_⟩
      dsimp only [updated]
      rw [lower_up_order]
      exact h
  | true =>
      obtain ⟨older, old, htop⟩ := exists_newest (hd rfl)
      obtain ⟨before, after, hsplit, hnew⟩ := lower_down_order_split w.ports side qc old older htop
      let start : Splice := {w with ports := w.ports.set (Group.onSide false side) older}
      obtain ⟨out, hout, hfront, hports⟩ := CyclicFrontier.splice_blocks_total (w := start) h hsplit
      refine ⟨out, ?_, ?_⟩
      · rw [attachOwner_down_eq w _ qc old older htop]
        exact hout
      · rw [hports]
        change CyclicFrontier out.mate (w.ports.set (Group.onSide false side) older).cyclic
        rw [hnew]
        exact hfront

/-- Both actual physical owner attachments succeed on the shared carrier.
The statement quantifies over the existing four labels rather than separate recurrences. -/
theorem physical_attach_cyclic_total (mate : List Nat) (p : Ports) (side : Side) (m : Move)
    (h : CyclicFrontier (mate.map some) p.cyclic)
    (hp : m.upperDown = true → p.get (Group.onSide true side) ≠ [])
    (hq : m.lowerDown = true → p.get (Group.onSide false side) ≠ []) :
    let initial : Splice := ⟨p, mate.map some ++ [some (mate.length + 1), some mate.length], 0⟩
    ∃ upper out, attachOwner initial (Group.onSide true side) m.upperDown mate.length = some upper ∧
      attachOwner upper (Group.onSide false side) m.lowerDown (mate.length + 1) = some out ∧
      CyclicFrontier out.mate out.ports.cyclic := by
  let initial : Splice := ⟨p, mate.map some ++ [some (mate.length + 1), some mate.length], 0⟩
  have hc : CyclicFrontier initial.mate (bothCupOrder initial.ports side
      mate.length (mate.length + 1)) := by
    simpa only [List.length_map] using h.appendCup_physical side
  obtain ⟨upper, hupper, hfront, hother⟩ :=
    upper_attach_cyclic_total initial side m.upperDown mate.length (mate.length + 1) hc hp
  obtain ⟨out, hout, hfinal⟩ := lower_attach_cyclic_total upper side m.lowerDown
    (mate.length + 1) hfront (by intro hd; rw [hother]; exact hq hd)
  exact ⟨upper, out, hupper, hout, hfinal⟩

/-- All raw slots become live `some` entries before local physical surgery. -/
theorem live_mapSome_iff (mate : List Nat) (i : Nat) :
    Live (mate.map some) i ↔ i < mate.length := by
  constructor
  · rintro ⟨j, hj⟩
    simpa only [List.length_map] using hj.bound
  · intro hi
    exact ⟨mate[i], (mapSome_hasMate mate i _).mpr (List.getElem?_eq_getElem hi)⟩

/-- Native input validation supplies the exact live cyclic frontier used by the physical proof. -/
theorem validKey_cyclicFrontier {s : RunSpec} {t : Stage} {x : Key}
    (h : validKey s t x = true) :
    CyclicFrontier (x.mate.map some) (Ports.ofLengths (geometry s t x.counters).length).cyclic := by
  obtain ⟨hlen, hp, hc⟩ := validKey_pairing_contract h
  let len := (geometry s t x.counters).length
  have hl : x.mate.length = len.pl + len.pr + len.ql + len.qr := by
    simpa only [Ports.flat_ofLengths, List.length_range] using hlen
  have hperm := Ports.cyclic_perm_range len
  refine ⟨pairingValid_mateInvariant hp, hperm.nodup_iff.mpr List.nodup_range, ?_, hc⟩
  intro i
  rw [hperm.mem_iff, List.mem_range, live_mapSome_iff, hl]

private theorem ofLengths_lengths (len : Counters) : (Ports.ofLengths len).lengths = len := by
  cases len
  simp [Ports.ofLengths, Ports.lengths]

/-- The executable reservoir guards imply actual nonempty newest-owner groups. -/
theorem moveAllowed_nonempty {s : RunSpec} {t : Stage} {x : Key} {side : Side} {m : Move}
    (h : moveAllowed s t x side m = true) :
    (m.upperDown = true →
      (Ports.ofLengths (geometry s t x.counters).length).get (Group.onSide true side) ≠ []) ∧
    (m.lowerDown = true →
      (Ports.ofLengths (geometry s t x.counters).length).get (Group.onSide false side) ≠ []) := by
  simp only [moveAllowed, Bool.and_eq_true] at h
  have hp := h.1.1.1.1
  have hq := h.1.1.1.2
  constructor
  · intro hd
    have hr : 0 < (geometry s t x.counters).reservoir.get (Group.onSide true side) := by
      simpa only [hd, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hp
    obtain ⟨older, old, htop⟩ := Ports.exists_newest_of_reservoir_pos (ofLengths_lengths _) hr
    rw [htop]
    simp
  · intro hd
    have hr : 0 < (geometry s t x.counters).reservoir.get (Group.onSide false side) := by
      simpa only [hd, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hq
    obtain ⟨older, old, htop⟩ := Ports.exists_newest_of_reservoir_pos (ofLengths_lengths _) hr
    rw [htop]
    simp

/-- The exact candidate's physical phase is total and planar whenever its original
input and physical-move guards pass. Drains and terminal acceptance remain separate. -/
theorem candidate_physical_cyclic_total {s : RunSpec} {t : Stage} {x : Key}
    {side : Side} {m : Move} (hx : validKey s t x = true)
    (hm : moveAllowed s t x side m = true) :
    let initial : Splice := ⟨Ports.ofLengths (geometry s t x.counters).length,
      x.mate.map some ++ [some (x.mate.length + 1), some x.mate.length], 0⟩
    ∃ upper out,
      attachOwner initial (Group.onSide true side) m.upperDown x.mate.length = some upper ∧
      attachOwner upper (Group.onSide false side) m.lowerDown (x.mate.length + 1) = some out ∧
      CyclicFrontier out.mate out.ports.cyclic :=
  physical_attach_cyclic_total x.mate _ side m (validKey_cyclicFrontier hx)
    (moveAllowed_nonempty hm).1 (moveAllowed_nonempty hm).2

end Meanders.FirstCrossing

namespace Meanders.FirstCrossing

/-- Renaming any storage-order segment uses its exact offset in the full list. -/
theorem map_idxOf_segment (before segment after : List Nat)
    (hn : (before ++ segment ++ after).Nodup) :
    segment.map (before ++ segment ++ after).idxOf =
      (List.range segment.length).map (before.length + ·) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have his : i < segment.length := by simpa using hi
    simp only [List.getElem_map, List.getElem_range]
    apply flat_idxOf hn
    have hlook : (before ++ segment ++ after)[before.length + i]? = some segment[i] := by
      rw [List.append_assoc, List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left his, List.getElem?_eq_getElem his]
    exact hlook

/-- Renaming the geometric cyclic order by storage indices produces exactly the
native canonical four-group cyclic order, including both reversed groups. -/
theorem Ports.cyclic_ofLengths_eq_map_idxOf (p : Ports) (hn : p.flat.Nodup) :
    (Ports.ofLengths p.lengths).cyclic = p.cyclic.map p.flat.idxOf := by
  have hpl := map_idxOf_segment [] p.pl (p.pr ++ p.ql ++ p.qr) (by
    simpa only [List.nil_append, List.append_assoc, Ports.flat] using hn)
  have hpr := map_idxOf_segment p.pl p.pr (p.ql ++ p.qr) (by
    simpa only [List.append_assoc, Ports.flat] using hn)
  have hql := map_idxOf_segment (p.pl ++ p.pr) p.ql p.qr hn
  have hqr := map_idxOf_segment (p.pl ++ p.pr ++ p.ql) p.qr [] (by simpa [Ports.flat] using hn)
  simp only [List.nil_append, List.length_nil, Nat.zero_add, List.append_nil,
    List.length_append, ← List.append_assoc] at hpl hpr hql hqr
  simp only [Ports.ofLengths, Ports.lengths, Ports.cyclic, List.map_append, List.map_reverse,
    Ports.flat, hpl, hpr, hql, hqr]
  simp

/-- List-based boundary names commute with pointwise relabelling. -/
theorem cyclicName_map {n : Nat} (names : List Nat) (hlen : names.length = 2 * n)
    (f : Nat → Nat) (i : Point n) :
    cyclicName (names.map f) (by simpa using hlen) i = f (cyclicName names hlen i) := by
  simp [cyclicName]

/-- The actual storage-index normalization preserves the cyclic noncrossing
checker, without using any post-normalization validation premise. -/
theorem normalize_cyclicCheck {c : Counters} {w : Splice} {out : Key}
    (hf : CyclicFrontier w.mate w.ports.cyclic) (h : normalize c w = some out) :
    cyclicCheck (out.mate.map some) (Ports.ofLengths w.ports.lengths).cyclic [] = true := by
  have hn : w.ports.flat.Nodup := w.ports.cyclic_perm_flat.nodup_iff.mp hf.nodup
  have hc : CoversLive w := fun x =>
    w.ports.cyclic_perm_flat.mem_iff.symm.trans (hf.covers x)
  obtain ⟨n, hlen, m, hr⟩ := exists_representsCyclic hf.nodup hf.pairing hf.covers hf.check
  let names := w.ports.cyclic.map w.ports.flat.idxOf
  have hnames : (Ports.ofLengths w.ports.lengths).cyclic = names :=
    w.ports.cyclic_ofLengths_eq_map_idxOf hn
  have hlen' : names.length = 2 * n := by simpa [names] using hlen
  have hnd : names.Nodup := by
    rw [← hnames]
    exact (Ports.cyclic_perm_range _).nodup_iff.mpr List.nodup_range
  have hrep : RepresentsCyclic (out.mate.map some) names hlen' m := by
    intro i j
    have hxmem : cyclicName w.ports.cyclic hlen i ∈ w.ports.flat :=
      w.ports.cyclic_perm_flat.mem_iff.mp (List.getElem_mem (by omega))
    have hymem : cyclicName w.ports.cyclic hlen j ∈ w.ports.flat :=
      w.ports.cyclic_perm_flat.mem_iff.mp (List.getElem_mem (by omega))
    change HasMate (out.mate.map some)
      (cyclicName (w.ports.cyclic.map w.ports.flat.idxOf) hlen' i)
      (cyclicName (w.ports.cyclic.map w.ports.flat.idxOf) hlen' j) ↔ _
    rw [cyclicName_map w.ports.cyclic hlen w.ports.flat.idxOf i,
      cyclicName_map w.ports.cyclic hlen w.ports.flat.idxOf j, hasMate_map_some,
      normalize_conjugates h hn hf.pairing hc
        (List.getElem?_idxOf hxmem) (List.getElem?_idxOf hymem)]
    exact hr i j
  rw [hnames]
  exact cyclicCheck_of_represents hnd hrep

end Meanders.FirstCrossing
