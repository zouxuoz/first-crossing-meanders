import Meanders.Models.FirstCrossing.Interpretation.SourceClosure
import Meanders.Models.FirstCrossing.Surgery.NativeTotal

/-!
# Cycle acceptance for the four actual physical-operation slots

The slots are the upper attachment, lower attachment, upper FIFO drain, and
lower FIFO drain. Each active slot uses its actual native splice and physical
source edge; an inactive slot leaves the cycle counter unchanged. These are
proof contracts for the existing operations, not an alternative recurrence.
-/

namespace Meanders.FirstCrossing

open SimpleGraph

/-- Consequences of one actual source operation for its unchanged cycle counter. -/
structure CycleStepFacts {spec : RunSpec} (s : Source spec) (next : Stage)
    (H J : SimpleGraph (Incidence spec.n)) (before after : Nat) : Prop where
  /-- Native splicing never removes a recorded closure. -/
  monotone : before ≤ after
  /-- One actual edge closes at most one path. -/
  increase : after ≤ before + 1
  /-- Closing a connected source saturates its complete physical incidence graph. -/
  complete : before < after → J = incidenceGraph s.matchings
  /-- A connected source cannot close before all physical visits have occurred. -/
  final : before < after → next.left + next.right = 2 * spec.n
  /-- There are no degree-one endpoints available after the full graph is present. -/
  saturated : H = incidenceGraph s.matchings → after = before

/-- U attachments and zero FIFO drains have no cycle effect. -/
theorem CycleStepFacts.of_unchanged {spec : RunSpec} {s : Source spec} {next : Stage}
    {H J : SimpleGraph (Incidence spec.n)} {before after : Nat} (h : after = before) :
    CycleStepFacts s next H J before after := by
  subst after
  exact ⟨le_rfl, by omega, fun h => by omega, fun h => by omega, fun _ => rfl⟩

/-- Every actual successful source-edge splice has the required cycle facts;
physical edge newness follows from the source event decomposition. -/
theorem Source.visit_splice_cycle_facts {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    {E : SimpleGraph (Incidence spec.n)} [DecidableRel E.Adj]
    (hE : E ≤ s.visitEdges hnext) {w out : Splice} {port : Nat → Incidence spec.n}
    (hm : MateInvariant w.mate) (hd : RepresentsDegreeOne (s.partialGraph t ⊔ E) w.mate port)
    (hp : RepresentsLivePaths w.mate (s.partialGraph t ⊔ E) port)
    (hconn : (incidenceGraph s.matchings).Connected)
    {x y a b : Nat} (hx : HasMate w.mate x a) (hy : HasMate w.mate y b) (hxy : x ≠ y)
    (hedge : (s.visitEdges hnext).Adj (port x) (port y))
    (hnot : ¬ E.Adj (port x) (port y)) (hj : spliceJoin w x y = some out) :
    CycleStepFacts s (t.next side) (s.partialGraph t ⊔ E)
      ((s.partialGraph t ⊔ E) ⊔ edge (port x) (port y)) w.cycles out.cycles := by
  classical
  have hc := (spliceJoin_result hm hx hy hxy hj).2.2.1
  have hsmall : w.cycles ≤ out.cycles ∧ out.cycles ≤ w.cycles + 1 := by
    split_ifs at hc <;> omega
  refine ⟨hsmall.1, hsmall.2, ?_, ?_, ?_⟩
  · intro hinc
    have hay : a = y := by split_ifs at hc <;> omega
    have hr := (hp x y ⟨a, hx⟩ ⟨b, hy⟩).mpr (Or.inr (hay ▸ hx))
    exact s.visit_closing_complete ht hnext hE hd hp hconn ⟨a, hx⟩ ⟨b, hy⟩
      hxy hr hedge hnot
  · intro hinc
    have hbound : (t.next side).left + (t.next side).right ≤ 2 * spec.n := by
      have := s.cut_le
      obtain ⟨hl, hr⟩ := hnext
      omega
    by_contra he
    have hlt : (t.next side).left + (t.next side).right < 2 * spec.n := by omega
    have hn := s.visit_splice_no_cycle_before_finish ht hnext hlt hE hm hd hp hconn
      hx hy hxy hedge hnot hj
    omega
  · intro hfull
    have he := (s.partialGraph_le _) ((s.visitEdges_iff_new ht hnext _ _).mp hedge).1
    exact False.elim ((s.visit_edge_new_after_prefix hnext hedge hnot) (hfull.symm ▸ he))

/-- The at-most-one-cycle invariant propagates through one actual operation slot. -/
theorem CycleStepFacts.propagate {spec : RunSpec} {s : Source spec} {next : Stage}
    {H J : SimpleGraph (Incidence spec.n)} {before after : Nat}
    (hf : CycleStepFacts s next H J before after) (hHJ : H ≤ J)
    (hJ : J ≤ incidenceGraph s.matchings)
    (hold : before ≤ 1 ∧ (0 < before → H = incidenceGraph s.matchings ∧
      next.left + next.right = 2 * spec.n)) :
    after ≤ 1 ∧ (0 < after → J = incidenceGraph s.matchings ∧
      next.left + next.right = 2 * spec.n) := by
  by_cases hzero : before = 0
  · refine ⟨by have := hf.increase; omega, ?_⟩
    intro hpos
    exact ⟨hf.complete (by omega), hf.final (by omega)⟩
  · have hp : 0 < before := by omega
    obtain ⟨hfull, htime⟩ := hold.2 hp
    have he := hf.saturated hfull
    refine ⟨by omega, fun _ => ⟨?_, htime⟩⟩
    exact le_antisymm hJ (hfull ▸ hHJ)

/-- The four native operation slots close at most one cycle. Any recorded cycle
already completes the source graph and occurs at the final physical visit. -/
theorem Source.four_slots_cycle_bound {spec : RunSpec} (s : Source spec) (next : Stage)
    {H₀ H₁ H₂ H₃ H₄ : SimpleGraph (Incidence spec.n)} {c₀ c₁ c₂ c₃ c₄ : Nat}
    (hzero : c₀ = 0)
    (h₁ : CycleStepFacts s next H₀ H₁ c₀ c₁)
    (h₂ : CycleStepFacts s next H₁ H₂ c₁ c₂)
    (h₃ : CycleStepFacts s next H₂ H₃ c₂ c₃)
    (h₄ : CycleStepFacts s next H₃ H₄ c₃ c₄)
    (h₀₁ : H₀ ≤ H₁) (h₁₂ : H₁ ≤ H₂) (h₂₃ : H₂ ≤ H₃) (h₃₄ : H₃ ≤ H₄)
    (hle : H₄ ≤ incidenceGraph s.matchings) :
    c₄ ≤ 1 ∧ (0 < c₄ → H₄ = incidenceGraph s.matchings ∧
      next.left + next.right = 2 * spec.n) := by
  have hz : c₀ ≤ 1 ∧ (0 < c₀ → H₀ = incidenceGraph s.matchings ∧
      next.left + next.right = 2 * spec.n) := ⟨by omega, fun h => by omega⟩
  have ha := h₁.propagate h₀₁ (h₁₂.trans (h₂₃.trans (h₃₄.trans hle))) hz
  have hb := h₂.propagate h₁₂ (h₂₃.trans (h₃₄.trans hle)) ha
  have hc := h₃.propagate h₂₃ (h₃₄.trans hle) hb
  exact h₄.propagate h₃₄ hle hc

/-- Full physical source degree leaves no retained live endpoint. -/
theorem CyclicFrontier.flat_empty_of_full_degree {spec : RunSpec} {s : Source spec}
    {w : Splice} {port : Nat → Incidence spec.n}
    {H : SimpleGraph (Incidence spec.n)} [DecidableRel H.Adj]
    (hf : CyclicFrontier w.mate w.ports.cyclic)
    (hd : RepresentsDegreeOne H w.mate port) (hfull : incidenceGraph s.matchings ≤ H) :
    w.ports.flat = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  have hl := (hf.flat.2 i).mp hi
  have hh := (hd (port i)).mpr ⟨i, hl, rfl⟩
  have hle := (incidenceGraph s.matchings).degree_le_of_le hfull (v := port i)
  rw [incidenceGraph_degree] at hle
  omega

/-- The original cycle rule follows from actual substep interpretation, without
assuming either cycle acceptance or successor-key validation. -/
theorem Source.cycleAccepted_of_four_slots {spec : RunSpec} (s : Source spec) (next : Stage)
    {H₀ H₁ H₂ H₃ H₄ : SimpleGraph (Incidence spec.n)} [DecidableRel H₄.Adj]
    {c₀ c₁ c₂ c₃ : Nat} {out : Splice} {port : Nat → Incidence spec.n}
    (hzero : c₀ = 0) (htick : next.tick = next.left + next.right)
    (h₁ : CycleStepFacts s next H₀ H₁ c₀ c₁)
    (h₂ : CycleStepFacts s next H₁ H₂ c₁ c₂)
    (h₃ : CycleStepFacts s next H₂ H₃ c₂ c₃)
    (h₄ : CycleStepFacts s next H₃ H₄ c₃ out.cycles)
    (h₀₁ : H₀ ≤ H₁) (h₁₂ : H₁ ≤ H₂) (h₂₃ : H₂ ≤ H₃) (h₃₄ : H₃ ≤ H₄)
    (hle : H₄ ≤ incidenceGraph s.matchings)
    (hf : CyclicFrontier out.mate out.ports.cyclic)
    (hd : RepresentsDegreeOne H₄ out.mate port) : CycleAccepted spec next out := by
  obtain ⟨hbound, hclose⟩ := s.four_slots_cycle_bound next hzero h₁ h₂ h₃ h₄
    h₀₁ h₁₂ h₂₃ h₃₄ hle
  by_cases hz : out.cycles = 0
  · exact Or.inl hz
  · obtain ⟨hfull, htime⟩ := hclose (by omega)
    right
    refine ⟨by omega, htick.trans htime, ?_⟩
    exact hf.flat_empty_of_full_degree hd hfull.ge

/-- An actual U-owner attachment keeps its cycle counter unchanged. -/
theorem attachOwner_up_cycles {w out : Splice} {g : Group} {cup : Nat}
    (h : attachOwner w g false cup = some out) : out.cycles = w.cycles := by
  cases h
  rfl

end Meanders.FirstCrossing
