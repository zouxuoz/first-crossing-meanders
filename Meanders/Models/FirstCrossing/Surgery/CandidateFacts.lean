import Meanders.Models.FirstCrossing.Native.Transition
import Meanders.Models.FirstCrossing.Surgery.PhysicalCyclic
import Meanders.Models.FirstCrossing.Surgery.Drain

/-!
# Successful native surgery exposes its actual intermediate states

These facts only unpack the executable transition. They introduce neither a
second recurrence nor assumptions about source representation or connectivity.
LOW uses the same two drain equations with their definitionally zero counts.
-/

namespace Meanders.FirstCrossing

/-- A successful candidate exposes both owner attachments and both prescribed
FIFO drains, together with every outer guard checked by the implementation. -/
theorem candidateSplice_factors {s : RunSpec} {t : Stage} {x : Key}
    {side : Side} {m : Move} {out : Splice}
    (h : candidateSplice s t x side m = some out) :
    let g := geometry s t x.counters
    let next := t.next side
    let new := geometry s next (moveCounters x.counters side m)
    let pOld := min g.emitted.pl g.emitted.pr
    let pNew := min new.emitted.pl new.emitted.pr
    let qOld := min g.emitted.ql g.emitted.qr
    let qNew := min new.emitted.ql new.emitted.qr
    let cup : Splice := ⟨Ports.ofLengths g.length,
      x.mate.map some ++ [some (x.mate.length + 1), some x.mate.length], 0⟩
    moveAllowed s t x side m = true ∧
      ∃ upper attached pdrained : Splice,
        attachOwner cup (Group.onSide true side) m.upperDown x.mate.length = some upper ∧
        attachOwner upper (Group.onSide false side) m.lowerDown (x.mate.length + 1) =
          some attached ∧
        cyclicCheck attached.mate attached.ports.cyclic [] = true ∧
        pOld ≤ pNew ∧ qOld ≤ qNew ∧
        drain (pNew - pOld) .pl .pr attached = some pdrained ∧
        drain (qNew - qOld) .ql .qr pdrained = some out ∧
        (s.sector ≠ .low → out.ports.lengths = new.length) ∧
        (0 < out.cycles → out.cycles = 1 ∧ next.tick = 2 * s.n ∧ out.ports.flat = []) := by
  dsimp only
  unfold candidateSplice at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i hm
    have hm' : moveAllowed s t x side m = true := by simpa using hm
    refine ⟨hm', ?_⟩
    cases hu : attachOwner
        ⟨Ports.ofLengths (geometry s t x.counters).length,
          x.mate.map some ++ [some (x.mate.length + 1), some x.mate.length], 0⟩
        (Group.onSide true side) m.upperDown x.mate.length with
    | none => simp [hu] at h
    | some upper =>
      simp only [hu, bind, Option.bind] at h
      cases ha : attachOwner upper (Group.onSide false side) m.lowerDown (x.mate.length + 1) with
      | none => simp [ha] at h
      | some attached =>
        simp only [ha] at h
        split at h
        · simp at h
        · rename_i hcheck
          have hcheck' : cyclicCheck attached.mate attached.ports.cyclic [] = true := by
            simpa using hcheck
          cases hs : s.sector with
          | low =>
            simp only [hs] at h
            have hout : attached = out := by
              split at h
              · split at h <;> simp_all
              · simpa using h
            subst out
            refine ⟨upper, attached, attached, rfl, ha, hcheck', ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [geometry, hs, Counters.zero]
            · simp [geometry, hs, Counters.zero]
            · simp [geometry, hs, Counters.zero]
            · simp [geometry, hs, Counters.zero]
            · simp
            · intro hpos
              simp only [hpos, reduceIte] at h
              split at h
              · simp at h
              · rename_i hc
                simpa using hc
          | high L u v =>
            simp only [hs] at h
            split at h
            · simp at h
            · rename_i hmono
              have hmono' :
                  min (geometry s t x.counters).emitted.pl
                    (geometry s t x.counters).emitted.pr ≤
                    min (geometry s (t.next side) (moveCounters x.counters side m)).emitted.pl
                      (geometry s (t.next side) (moveCounters x.counters side m)).emitted.pr ∧
                  min (geometry s t x.counters).emitted.ql
                    (geometry s t x.counters).emitted.qr ≤
                    min (geometry s (t.next side) (moveCounters x.counters side m)).emitted.ql
                      (geometry s (t.next side) (moveCounters x.counters side m)).emitted.qr := by
                simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] using hmono
              cases hp : drain
                  (min (geometry s (t.next side) (moveCounters x.counters side m)).emitted.pl
                    (geometry s (t.next side) (moveCounters x.counters side m)).emitted.pr -
                    min (geometry s t x.counters).emitted.pl
                      (geometry s t x.counters).emitted.pr) .pl .pr attached with
              | none => simp [hp] at h
              | some pdrained =>
                simp only [hp] at h
                cases hq : drain
                    (min (geometry s (t.next side) (moveCounters x.counters side m)).emitted.ql
                      (geometry s (t.next side) (moveCounters x.counters side m)).emitted.qr -
                      min (geometry s t x.counters).emitted.ql
                        (geometry s t x.counters).emitted.qr) .ql .qr pdrained with
                | none => simp [hq] at h
                | some drained =>
                  simp only [hq] at h
                  split at h
                  · simp at h
                  · rename_i hlength
                    have hlength' : drained.ports.lengths =
                        (geometry s (t.next side) (moveCounters x.counters side m)).length := by
                      cases he : drained.ports.lengths
                      cases hn : (geometry s (t.next side) (moveCounters x.counters side m)).length
                      simp_all [bne, BEq.beq, instBEqCounters.beq]
                    have hout : drained = out := by
                      split at h
                      · split at h <;> simp_all
                      · simpa using h
                    subst out
                    refine ⟨upper, attached, pdrained, rfl, ha, hcheck', hmono'.1, hmono'.2,
                      hp, hq, fun _ => hlength', ?_⟩
                    intro hpos
                    simp only [hpos, reduceIte] at h
                    split at h
                    · simp at h
                    · rename_i hc
                      simpa using hc

/-- Successful normalization exposes the actual preceding surgery state. -/
theorem candidate_factors {s : RunSpec} {t : Stage} {x y : Key} {side : Side} {m : Move}
    (h : candidate s t x side m = some y) :
    ∃ out, candidateSplice s t x side m = some out ∧
      normalize (moveCounters x.counters side m) out = some y := by
  unfold candidate at h
  cases hw : candidateSplice s t x side m with
  | none => simp [hw] at h
  | some out => exact ⟨out, rfl, by simpa only [hw, Option.bind_some] using h⟩

end Meanders.FirstCrossing

/-! Native validation supplies all live/fresh premises for the two actual owner attachments. -/

namespace Meanders.FirstCrossing

/-- Input guards and actual attachment results supply every physical live/fresh fact.
Neither a successor graph interpretation nor a successful output validation is assumed. -/
theorem candidate_attachment_facts {s : RunSpec} {t : Stage} {x : Key}
    {side : Side} {m : Move} (hx : validKey s t x = true)
    (hm : moveAllowed s t x side m = true) :
    let initial : Splice := ⟨Ports.ofLengths (geometry s t x.counters).length,
      x.mate.map some ++ [some (x.mate.length + 1), some x.mate.length], 0⟩
    ∀ {upper attached : Splice},
      attachOwner initial (Group.onSide true side) m.upperDown x.mate.length = some upper →
      attachOwner upper (Group.onSide false side) m.lowerDown (x.mate.length + 1) = some attached →
      MateInvariant initial.mate ∧
      (∀ i ∈ initial.ports.get (Group.onSide true side), Live initial.mate i) ∧
      Live initial.mate x.mate.length ∧
      x.mate.length ∉ initial.ports.get (Group.onSide true side) ∧
      (∀ i ∈ upper.ports.get (Group.onSide false side), Live upper.mate i) ∧
      Live upper.mate (x.mate.length + 1) ∧
      x.mate.length + 1 ∉ upper.ports.get (Group.onSide false side) ∧
      attached.ports.flat.Nodup ∧ CoversLive attached := by
  dsimp only
  let initial : Splice := ⟨Ports.ofLengths (geometry s t x.counters).length,
    x.mate.map some ++ [some (x.mate.length + 1), some x.mate.length], 0⟩
  intro upper attached hu hq
  have hbase := validKey_cyclicFrontier hx
  have hstart : CyclicFrontier initial.mate
      (bothCupOrder initial.ports side x.mate.length (x.mate.length + 1)) := by
    simpa only [initial, List.length_map] using hbase.appendCup_physical side
  obtain ⟨upper', hu', hupper, hother⟩ := upper_attach_cyclic_total initial side
    m.upperDown x.mate.length (x.mate.length + 1) hstart (moveAllowed_nonempty hm).1
  have hue : upper' = upper := Option.some.inj (hu'.symm.trans hu)
  subst upper'
  obtain ⟨attached', hq', hfinal⟩ := lower_attach_cyclic_total upper side
    m.lowerDown (x.mate.length + 1) hupper (by
      intro hd
      rw [hother]
      exact (moveAllowed_nonempty hm).2 hd)
  have hqe : attached' = attached := Option.some.inj (hq'.symm.trans hq)
  subst attached'
  have hbound (g : Group) {i : Nat} (hi : i ∈ initial.ports.get g) : i < x.mate.length := by
    have hflat : i ∈ initial.ports.flat := (Ports.mem_flat_iff _ _).mpr ⟨g, hi⟩
    have hcyclic := initial.ports.cyclic_perm_flat.mem_iff.mpr hflat
    simpa only [List.length_map] using hbase.name_bound hcyclic
  refine ⟨hstart.pairing, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (hstart.covers i).mp (upper_mem_bothCupOrder _ _ _ _ _ hi)
  · exact (hstart.covers _).mp (mem_bothCupOrder _ _ _ _).1
  · intro hi
    exact Nat.lt_irrefl _ (hbound _ hi)
  · intro i hi
    exact (hupper.covers i).mp (lower_mem_lowerCupOrder _ _ _ _ hi)
  · exact (hupper.covers _).mp (mem_lowerCupOrder _ _ _)
  · rw [hother]
    intro hi
    have hh := hbound _ hi
    omega
  · exact attached.ports.cyclic_perm_flat.nodup_iff.mp hfinal.nodup
  · intro i
    exact attached.ports.cyclic_perm_flat.mem_iff.symm.trans (hfinal.covers i)

end Meanders.FirstCrossing
