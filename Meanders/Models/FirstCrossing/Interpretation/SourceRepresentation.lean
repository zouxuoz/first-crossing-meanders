import Meanders.Models.FirstCrossing.Interpretation.SourceProgress
import Meanders.Models.FirstCrossing.Interpretation.AttachmentStep
import Meanders.Models.FirstCrossing.Surgery.ClosingComponent

/-!
# Canonical physical naming for source keys

The actual retained source boundary supplies the physical interpretation of every
raw array slot. Positive rank supplies an irrelevant default outside the live
domain. Initial and terminal statements come from source words and physical
coverage, independently of successor validation guards.
-/

namespace Meanders.FirstCrossing

/-- Source boundary positions provide exact degree-one coverage whenever the raw
live names enumerate that fixed boundary. This is supplied by key normalization. -/
theorem Source.boundary_degreeOne {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) {mate : List (Option ℕ)} {port : ℕ → Incidence spec.n}
    (hlive : ∀ i, Live mate i ↔ i < (s.retainedBoundary ht).length)
    (hport : ∀ i (hi : i < (s.retainedBoundary ht).length),
      port i = (s.retainedBoundary ht)[i]) :
    RepresentsDegreeOne (s.partialGraph t) mate port := by
  intro v
  rw [← s.mem_retainedBoundary_iff_degree_one ht v, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i, (hlive i).mpr hi, (hport i hi).trans he⟩
  · rintro ⟨i, hi, he⟩
    have hb := (hlive i).mp hi
    exact ⟨i, hb, (hport i hb).symm.trans he⟩

/-- Duplicate-free actual source boundary names give the live injectivity needed
when degree-one coverage is transported through later edge substeps. -/
theorem Source.boundary_live_injective {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) {mate : List (Option ℕ)} {port : ℕ → Incidence spec.n}
    (hlive : ∀ i, Live mate i ↔ i < (s.retainedBoundary ht).length)
    (hport : ∀ i (hi : i < (s.retainedBoundary ht).length),
      port i = (s.retainedBoundary ht)[i]) : Set.InjOn port {i | Live mate i} := by
  intro i hi j hj he
  have hib := (hlive i).mp hi
  have hjb := (hlive j).mp hj
  rw [hport i hib, hport j hjb] at he
  exact (s.retainedBoundary_nodup ht).getElem_inj_iff.mp he

/-- A raw key has one live name at every array position and no other live names. -/
theorem mapSome_live_iff (mate : List ℕ) (i : ℕ) :
    Live (mate.map some) i ↔ i < mate.length := by
  constructor
  · rintro ⟨j, hj⟩
    simpa only [List.length_map] using hj.bound
  · intro hi
    exact ⟨mate[i], (mapSome_hasMate _ _ _).mpr (List.getElem?_eq_getElem hi)⟩

/-- The fixed source-key interpretation supplies the raw live path relation used
by every physical substep; no successor path relation is assumed. -/
theorem Source.RepresentsKey.livePaths {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {key : Key} (hk : s.RepresentsKey ht key)
    {port : ℕ → Incidence spec.n}
    (hport : ∀ i (hi : i < (s.retainedBoundary ht).length),
      port i = (s.retainedBoundary ht)[i]) :
    RepresentsLivePaths (key.mate.map some) (s.partialGraph t) port := by
  intro i j hi hj
  have hib : i < (s.retainedBoundary ht).length := by
    rw [← hk.2.1]
    exact (mapSome_live_iff _ _).mp hi
  have hjb : j < (s.retainedBoundary ht).length := by
    rw [← hk.2.1]
    exact (mapSome_live_iff _ _).mp hj
  rw [hport i hib, hport j hjb, mapSome_hasMate]
  simpa only [Fin.ext_iff] using hk.2.2 ⟨i, hib⟩ ⟨j, hjb⟩

/-- The actual source boundary interpretation immediately supplies exact
physical degree-one coverage and duplicate-free live names for the raw key. -/
theorem Source.RepresentsKey.degreeOne {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {key : Key} (hk : s.RepresentsKey ht key)
    {port : ℕ → Incidence spec.n}
    (hport : ∀ i (hi : i < (s.retainedBoundary ht).length),
      port i = (s.retainedBoundary ht)[i]) :
    RepresentsDegreeOne (s.partialGraph t) (key.mate.map some) port ∧
      Set.InjOn port {i | Live (key.mate.map some) i} := by
  have hlive : ∀ i, Live (key.mate.map some) i ↔ i < (s.retainedBoundary ht).length := by
    intro i
    rw [mapSome_live_iff, hk.2.1]
  exact ⟨s.boundary_degreeOne ht hlive hport, s.boundary_live_injective ht hlive hport⟩

/-- The total canonical naming function agrees with the physical retained list
on its finite domain; the fallback is never used by live slots. -/
noncomputable def Source.boundaryPort {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (hn : 0 < spec.n) (i : ℕ) : Incidence spec.n :=
  ((s.retainedBoundary ht)[i]?).getD (true, ⟨0, by omega⟩)

/-- Exact canonical port lookup at an original retained boundary position. -/
theorem Source.boundaryPort_eq {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (hn : 0 < spec.n) (i : ℕ)
    (hi : i < (s.retainedBoundary ht).length) :
    s.boundaryPort ht hn i = (s.retainedBoundary ht)[i] := by
  simp only [Source.boundaryPort, List.getElem?_eq_getElem hi, Option.getD_some]

/-- Canonical naming supplies every local raw-path and degree-one invariant. -/
theorem Source.RepresentsKey.canonical_invariants {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {key : Key} (hk : s.RepresentsKey ht key)
    (hn : 0 < spec.n) (hpair : pairingValid key.mate = true) :
    MateInvariant (key.mate.map some) ∧
      RepresentsLivePaths (key.mate.map some) (s.partialGraph t) (s.boundaryPort ht hn) ∧
      RepresentsDegreeOne (s.partialGraph t) (key.mate.map some) (s.boundaryPort ht hn) ∧
      Set.InjOn (s.boundaryPort ht hn) {i | Live (key.mate.map some) i} :=
  ⟨pairingValid_mateInvariant hpair, hk.livePaths (s.boundaryPort_eq ht hn),
    hk.degreeOne (s.boundaryPort_eq ht hn)⟩

/-- Temporary candidate names agree with the unchanged source boundary before the cup. -/
theorem Source.candidatePort_old {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (i : ℕ) (hi : i < (s.retainedBoundary ht).length) :
    s.candidatePort ht hnext i = (s.retainedBoundary ht)[i] := by
  simp [Source.candidatePort, Source.candidateBoundary, List.getElem?_append, hi]

/-- An unvisited incidence is isolated in the actual processed source graph. -/
theorem Source.unvisited_isolated {spec : RunSpec} (s : Source spec)
    (t : Stage) (a : Incidence spec.n) (ha : ¬ visited t a.2) (v : Incidence spec.n) :
    (s.partialGraph t).Reachable a v ↔ v = a := by
  constructor
  · intro hr
    by_contra hne
    have hp := hr.degree_pos_left (Ne.symm hne)
    have hd := s.partialGraph_degree t a
    rw [ite_eq_right ha] at hd
    omega
  · rintro rfl
    exact SimpleGraph.Reachable.refl _

/-- The exact native candidate cup represents its fresh physical crossing edge. -/
theorem Source.RepresentsKey.candidateCup_paths {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {key : Key} (hk : s.RepresentsKey ht key)
    {side : Side} (hnext : s.Progress (t.next side)) (hpair : pairingValid key.mate = true) :
    RepresentsLivePaths
      (key.mate.map some ++ [some (key.mate.length + 1), some key.mate.length])
      (s.partialGraph t ⊔ SimpleGraph.edge (true, s.newPoint hnext) (false, s.newPoint hnext))
      (s.candidatePort ht hnext) := by
  have hu : s.candidatePort ht hnext key.mate.length = (true, s.newPoint hnext) := by
    rw [hk.2.1, s.candidatePort_upper]
  have hl : s.candidatePort ht hnext (key.mate.length + 1) = (false, s.newPoint hnext) := by
    rw [hk.2.1, s.candidatePort_lower]
  have hc := candidateCup_represents hpair
    (hk.livePaths (s.candidatePort_old ht hnext))
    (by rw [hk.2.1]; exact s.candidatePort_injective ht hnext)
    (by
      intro v
      rw [hu]
      exact s.unvisited_isolated t _ (s.newPoint_not_visited hnext) v)
    (by
      intro v
      rw [hl]
      exact s.unvisited_isolated t _ (s.newPoint_not_visited hnext) v)
  simpa only [hu, hl] using hc

/-- The completed physical source has no degree-one endpoints, hence no retained ports. -/
theorem Source.retainedBoundary_end {spec : RunSpec} (s : Source spec) :
    s.retainedBoundary (s.ofTick_progress (2 * spec.n)) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  have hd := (s.mem_retainedBoundary_iff_degree_one (s.ofTick_progress _) a).mp ha
  have hdeg := s.partialGraph_degree (Stage.ofTick spec (2 * spec.n)) a
  rw [ite_eq_left (s.visited_ofTick_end a.2),
    ite_eq_left (s.matchingProcessed_end a.1 a.2)] at hdeg
  omega

/-- The final original counters equal the full budget tuple, component by component. -/
theorem Source.counters_end {spec : RunSpec} (s : Source spec) :
    s.counters (Stage.ofTick spec (2 * spec.n)) = spec.budgets := by
  have hpl := s.counters_end_get .pl
  have hpr := s.counters_end_get .pr
  have hql := s.counters_end_get .ql
  have hqr := s.counters_end_get .qr
  cases hc : s.counters (Stage.ofTick spec (2 * spec.n))
  cases hb : spec.budgets
  simp only [hc, hb, Counters.get] at hpl hpr hql hqr
  cases hpl
  cases hpr
  cases hql
  cases hqr
  rfl

/-- Any represented terminal key has the exhausted original budgets and an empty mate array. -/
theorem Source.RepresentsKey.terminal {spec : RunSpec} {s : Source spec} {key : Key}
    (hk : s.RepresentsKey (s.ofTick_progress (2 * spec.n)) key) :
    key.counters = spec.budgets ∧ key.mate = [] := by
  refine ⟨hk.1.trans s.counters_end, ?_⟩
  have hl := hk.2.1
  rw [s.retainedBoundary_end, List.length_nil] at hl
  exact List.length_eq_zero_iff.mp hl

/-- A single covered terminal cycle proves the public source overlay connected. -/
theorem Source.connected_of_terminal_one_cycle {spec : RunSpec} (s : Source spec)
    {w : Splice} {port : ℕ → Incidence spec.n} {closed : List (Incidence spec.n)}
    (hcover : CoversProcessed w.mate (s.partialGraph (Stage.ofTick spec (2 * spec.n)))
      port closed (fun a => visited (Stage.ofTick spec (2 * spec.n)) a.2))
    (hcount : closed.length = w.cycles) (hone : w.cycles = 1)
    (hempty : ∀ i, ¬ Live w.mate i) : (unionGraph s.matchings).Connected := by
  have hc := hcover.connected_of_one_cycle hcount hone hempty (fun a => s.visited_ofTick_end a.2)
  rw [s.partialGraph_end] at hc
  exact (incidenceGraph_connected_iff s.matchings).mp hc

end Meanders.FirstCrossing
