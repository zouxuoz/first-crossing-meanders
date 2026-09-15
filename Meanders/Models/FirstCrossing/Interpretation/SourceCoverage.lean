import Meanders.Models.FirstCrossing.Interpretation.Preservation
import Meanders.Models.FirstCrossing.Surgery.ClosingComponent

/-!
# Processed-component coverage for actual source transitions

Before the final visit every processed incidence reaches a retained endpoint.
During a visit, proof-only closed witnesses track the actual cycle counter.
This information is transported separately from the live-path interpretation.
-/

namespace Meanders.FirstCrossing

open SimpleGraph

/-- Changing only unused names does not change processed-component coverage. -/
theorem CoversProcessed.port_congr {V : Type*} {mate : List (Option Nat)}
    {G : SimpleGraph V} {port other : Nat → V} {closed : List V} {processed : V → Prop}
    (hc : CoversProcessed mate G port closed processed)
    (he : ∀ i, Live mate i → port i = other i) :
    CoversProcessed mate G other closed processed := by
  intro v hv
  rcases hc v hv with ⟨i, hi, hr⟩ | hclosed
  · exact Or.inl ⟨i, hi, he i hi ▸ hr⟩
  · exact Or.inr hclosed

/-- Actual normalization transports every old live witness to its storage index. -/
theorem normalize_covers {V : Type*} {c : Counters} {w : Splice} {out : Key}
    {G : SimpleGraph V} {port : Nat → V} {closed : List V} {processed : V → Prop}
    (h : normalize c w = some out) (hl : CoversLive w)
    (hc : CoversProcessed w.mate G port closed processed) :
    CoversProcessed (out.mate.map some) G (normalizedPort w port) closed processed := by
  intro v hv
  rcases hc v hv with ⟨i, hi, hr⟩ | hclosed
  · have hm := (hl i).mpr hi
    have hb : w.ports.flat.idxOf i < out.mate.length := by
      rw [normalize_length h]
      exact List.idxOf_lt_length_iff.mpr hm
    refine Or.inl ⟨w.ports.flat.idxOf i, (mapSome_live_iff _ _).mpr hb, ?_⟩
    rw [normalizedPort_eq (List.getElem?_idxOf hm)]
    exact hr
  · exact Or.inr hclosed

/-- No processed physical component has lost all retained endpoints before the
terminal visit. The canonical fallback is irrelevant to live names. -/
def Source.CoveredKey {spec : RunSpec} (s : Source spec) {t : Stage}
    (ht : s.Progress t) (x : Key) (hn : 0 < spec.n) : Prop :=
  CoversProcessed (x.mate.map some) (s.partialGraph t) (s.boundaryPort ht hn) []
    (fun a => visited t a.2)

/-- The empty initial stage covers its empty processed set. -/
theorem Source.coveredKey_initial {spec : RunSpec} (s : Source spec) (hn : 0 < spec.n) :
    s.CoveredKey (t := ⟨0, 0, 0⟩) ⟨Nat.zero_le _, Nat.zero_le _⟩ Key.empty hn := by
  intro a ha
  simp [visited] at ha

/-- A represented key's coverage can use the shared fresh candidate naming. -/
theorem Source.CoveredKey.candidatePort {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x : Key} {hn : 0 < spec.n}
    (hc : s.CoveredKey ht x hn) (hx : s.RepresentsKey ht x)
    {side : Side} (hnext : s.Progress (t.next side)) :
    CoversProcessed (x.mate.map some) (s.partialGraph t) (s.candidatePort ht hnext) []
      (fun a => visited t a.2) := by
  apply hc.port_congr
  intro i hi
  have hb : i < (s.retainedBoundary ht).length := by
    rw [← hx.2.1]
    exact (mapSome_live_iff _ _).mp hi
  rw [s.boundaryPort_eq ht hn i hb, s.candidatePort_old ht hnext i hb]

/-- Cup creation covers precisely the newly visited physical point as well as
all earlier processed incidences. -/
theorem Source.CoveredKey.candidateCup {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x : Key} {hn : 0 < spec.n}
    (hc : s.CoveredKey ht x hn) (hx : s.RepresentsKey ht x)
    {side : Side} (hnext : s.Progress (t.next side)) :
    CoversProcessed
      (x.mate.map some ++ [some (x.mate.length + 1), some x.mate.length])
      (s.partialGraph t ⊔ edge (true, s.newPoint hnext) (false, s.newPoint hnext))
      (s.candidatePort ht hnext) [] (fun a => visited (t.next side) a.2) := by
  have hp : s.candidatePort ht hnext x.mate.length = (true, s.newPoint hnext) := by
    rw [hx.2.1, s.candidatePort_upper]
  have hq : s.candidatePort ht hnext (x.mate.length + 1) = (false, s.newPoint hnext) := by
    rw [hx.2.1, s.candidatePort_lower]
  have hcup := appendCup_covers (hc.candidatePort hx hnext)
  simp only [List.length_map, hp, hq] at hcup
  intro a ha
  apply hcup a
  rcases (s.visited_next_iff hnext a.2).mp ha with hold | hnew
  · exact Or.inl hold
  · rcases a with ⟨owner, a⟩
    cases owner
    · exact Or.inr (Or.inr (Prod.ext rfl hnew))
    · exact Or.inr (Or.inl (Prod.ext rfl hnew))

/-- Exact native physical surgery preserves coverage, retaining one witness
for each cycle counted during this visit. -/
theorem Source.CoveredKey.physical_visit {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x : Key} {hn : 0 < spec.n}
    (hcover : s.CoveredKey ht x hn) (hx : s.RepresentsKey ht x)
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
      ∃ closed, CoversProcessed out.mate (s.partialGraph (t.next side))
        (s.candidatePort ht hnext) closed (fun a => visited (t.next side) a.2) ∧
        closed.length = out.cycles := by
  dsimp only
  intro upper attached drained out hup hlo hpdrain hqdrain
  have hmove := s.nextMove_allowed ht hnext x hx.1
  obtain ⟨hmi, hplive, hpc, hpfresh, hqlive, hqc, hqfresh, hn, hc⟩ :=
    candidate_attachment_facts hvalid hmove hup hlo
  have hpair := (validKey_pairing_contract hvalid).2.1
  have hcup := hx.candidateCup_paths hnext hpair
  obtain ⟨_, _, _, _, _, _, _, closed, hclosed, hcount⟩ :=
    physical_visit_preserves hmi hcup (hcover.candidateCup hx hnext) rfl
      hplive hpc hpfresh hqlive hqc hqfresh hup hlo hn hc
      (s.joined_next_between t side .pl).2 (s.joined_next_between t side .ql).2
      hpdrain hqdrain
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
  rw [hgraph, ← s.partialGraph_next_decomposition ht hnext] at hclosed
  exact ⟨closed, hclosed, hcount⟩

/-- Successful checked surgery supplies coverage independently of its live-path theorem. -/
theorem Source.CoveredKey.candidateSplice {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x : Key} {hn : 0 < spec.n}
    (hc : s.CoveredKey ht x hn) (hx : s.RepresentsKey ht x)
    (hvalid : validKey spec t x = true) {side : Side} (hnext : s.Progress (t.next side))
    {out : Splice}
    (h : FirstCrossing.candidateSplice spec t x side (s.nextMove t side) = some out) :
    ∃ closed, CoversProcessed out.mate (s.partialGraph (t.next side))
      (s.candidatePort ht hnext) closed (fun a => visited (t.next side) a.2) ∧
      closed.length = out.cycles := by
  obtain ⟨_, upper, attached, drained, hup, hlo, _, _, _, hp, hq, _, _⟩ :=
    candidateSplice_factors h
  rw [hx.1, s.nextMove_counters] at hp hq
  change drain (s.joined (t.next side) .pl - s.joined t .pl) .pl .pr attached =
    some drained at hp
  change drain (s.joined (t.next side) .ql - s.joined t .ql) .ql .qr drained = some out at hq
  exact hc.physical_visit hx hvalid hnext hup hlo hp hq

/-- Physical group order transports normalized coverage to the canonical boundary naming. -/
theorem Source.normalize_covers {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (hn : 0 < spec.n) {w : Splice} {out : Key}
    (port : Nat → Incidence spec.n) {closed : List (Incidence spec.n)}
    (hl : CoversLive w)
    (hc : CoversProcessed w.mate (s.partialGraph t) port closed (fun a => visited t a.2))
    (hgroups : ∀ g, (w.ports.get g).map port = s.retainedGroup ht g)
    (h : normalize (s.counters t) w = some out) :
    CoversProcessed (out.mate.map some) (s.partialGraph t) (s.boundaryPort ht hn)
      closed (fun a => visited t a.2) := by
  apply (FirstCrossing.normalize_covers h hl hc).port_congr
  intro i hi
  have hb : i < w.ports.flat.length := by
    rw [← normalize_length h]
    exact (mapSome_live_iff _ _).mp hi
  have hmap := s.flat_map_eq_boundary ht port w.ports hgroups
  have hlen : w.ports.flat.length = (s.retainedBoundary ht).length := by
    simpa only [List.length_map] using congrArg List.length hmap
  have hi' : i < (s.retainedBoundary ht).length := by omega
  have hlookup := List.getElem?_eq_getElem (l := w.ports.flat) hb
  have hnames : (w.ports.flat.map port)[i]? = some ((s.retainedBoundary ht)[i]) := by
    rw [hmap]
    exact List.getElem?_eq_getElem hi'
  rw [List.getElem?_map, hlookup, Option.map_some] at hnames
  rw [normalizedPort_eq hlookup, s.boundaryPort_eq ht hn i hi']
  exact Option.some.inj hnames

/-- Before the terminal tick the actual cycle guard forces the temporary closed
witness list to remain empty, so coverage descends to the normalized key. -/
theorem Source.CoveredKey.candidate {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x y : Key} {hn : 0 < spec.n}
    (hc : s.CoveredKey ht x hn) (hx : s.RepresentsKey ht x)
    (hvalid : validKey spec t x = true) {side : Side} (hnext : s.Progress (t.next side))
    (hbefore : (t.next side).tick < 2 * spec.n)
    (h : FirstCrossing.candidate spec t x side (s.nextMove t side) = some y) :
    s.CoveredKey hnext y hn := by
  obtain ⟨out, hout, hnorm⟩ := candidate_factors h
  obtain ⟨closed, hcovered, hcount⟩ := hc.candidateSplice hx hvalid hnext hout
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcycle⟩ := candidateSplice_factors hout
  have hzero : out.cycles = 0 := by
    by_contra hne
    have hh := hcycle (by omega)
    omega
  have hclosed : closed = [] := List.length_eq_zero_iff.mp (hcount.trans hzero)
  subst closed
  obtain ⟨_, _, _, hlive, hgroups⟩ := hx.candidateSplice_paths hvalid hnext hout
  rw [hx.1, s.nextMove_counters] at hnorm
  exact s.normalize_covers hnext hn (s.candidatePort ht hnext) hlive hcovered hgroups hnorm

/-- A successful nonterminal raw source step preserves component coverage. -/
theorem Source.CoveredKey.rawStep {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x y : Key} {hn : 0 < spec.n}
    (hc : s.CoveredKey ht x hn) (hx : s.RepresentsKey ht x)
    {side : Side} (hnext : s.Progress (t.next side))
    (hschedule : spec.schedule[t.tick]? = some side)
    (hbefore : (t.next side).tick < 2 * spec.n)
    (h : FirstCrossing.rawStep spec t x (s.nextMove t side) = some y) :
    s.CoveredKey hnext y hn := by
  unfold FirstCrossing.rawStep at h
  split at h
  · rename_i hvalid
    rw [hschedule] at h
    cases hcan : FirstCrossing.candidate spec t x side (s.nextMove t side) with
    | none => simp [hcan] at h
    | some z =>
      simp only [hcan] at h
      split at h
      · cases h
        exact hc.candidate hx hvalid hnext hbefore hcan
      · contradiction
  · contradiction

/-- At completion every physical vertex is covered and every retained group is
empty. Coverage forces a real closed witness; the actual guard then makes it unique. -/
theorem Source.CoveredKey.candidateSplice_terminal_connected {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x : Key} {hn : 0 < spec.n}
    (hc : s.CoveredKey ht x hn) (hx : s.RepresentsKey ht x)
    (hvalid : validKey spec t x = true) {side : Side} (hnext : s.Progress (t.next side))
    (hend : t.next side = Stage.ofTick spec (2 * spec.n))
    {out : Splice}
    (h : FirstCrossing.candidateSplice spec t x side (s.nextMove t side) = some out) :
    (unionGraph s.matchings).Connected := by
  obtain ⟨closed, hcovered, hcount⟩ := hc.candidateSplice hx hvalid hnext h
  obtain ⟨_, _, _, hlive, hgroups⟩ := hx.candidateSplice_paths hvalid hnext h
  have hmap := s.flat_map_eq_boundary hnext (s.candidatePort ht hnext) out.ports hgroups
  have hboundary : s.retainedBoundary hnext = [] := by
    simpa only [hend] using s.retainedBoundary_end
  have hflat : out.ports.flat = [] := by
    apply List.length_eq_zero_iff.mp
    have hh := congrArg List.length hmap
    simpa only [List.length_map, hboundary, List.length_nil] using hh
  have hempty : ∀ i, ¬ Live out.mate i := by
    intro i hi
    have hh := (hlive i).mpr hi
    simp only [hflat, List.not_mem_nil] at hh
  have hpos : 0 < out.cycles := by
    let a : Incidence spec.n := (true, ⟨0, by omega⟩)
    have hv : visited (t.next side) a.2 := by
      rw [hend]
      exact s.visited_ofTick_end a.2
    rcases hcovered a hv with ⟨i, hi, _⟩ | ⟨c, hm, _⟩
    · exact False.elim (hempty i hi)
    · have hh := List.length_pos_of_mem hm
      omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcycle⟩ := candidateSplice_factors h
  apply s.connected_of_terminal_one_cycle (w := out) (closed := closed)
    (port := s.candidatePort ht hnext) _ hcount (hcycle hpos).1 hempty
  simpa only [hend] using hcovered

/-- A successful final normalized source candidate proves the source connected. -/
theorem Source.CoveredKey.candidate_terminal_connected {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x y : Key} {hn : 0 < spec.n}
    (hc : s.CoveredKey ht x hn) (hx : s.RepresentsKey ht x)
    (hvalid : validKey spec t x = true) {side : Side} (hnext : s.Progress (t.next side))
    (hend : t.next side = Stage.ofTick spec (2 * spec.n))
    (h : FirstCrossing.candidate spec t x side (s.nextMove t side) = some y) :
    (unionGraph s.matchings).Connected := by
  obtain ⟨out, hout, _⟩ := candidate_factors h
  exact hc.candidateSplice_terminal_connected hx hvalid hnext hend hout

/-- The final successful actual raw step closes exactly one covered source
component. No source-connectedness premise or terminal path-only inference is used. -/
theorem Source.CoveredKey.rawStep_terminal_connected {spec : RunSpec} {s : Source spec}
    {t : Stage} {ht : s.Progress t} {x y : Key} {hn : 0 < spec.n}
    (hc : s.CoveredKey ht x hn) (hx : s.RepresentsKey ht x)
    {side : Side} (hnext : s.Progress (t.next side))
    (hschedule : spec.schedule[t.tick]? = some side)
    (hendtick : (t.next side).tick = 2 * spec.n)
    (h : FirstCrossing.rawStep spec t x (s.nextMove t side) = some y) :
    (unionGraph s.matchings).Connected := by
  have hend : t.next side = Stage.ofTick spec (2 * spec.n) := by
    obtain ⟨side', hs', hv⟩ := rawStep_valid h
    have hside : side' = side := Option.some.inj (hs'.symm.trans hschedule)
    subst side'
    simp only [validKey, Bool.and_eq_true] at hv
    have he := (of_decide_eq_true hv.1.1.1.1.1.2).2
    simpa only [hendtick] using he
  unfold FirstCrossing.rawStep at h
  split at h
  · rename_i hvalid
    rw [hschedule] at h
    cases hcan : FirstCrossing.candidate spec t x side (s.nextMove t side) with
    | none => simp [hcan] at h
    | some z =>
      simp only [hcan] at h
      split at h
      · cases h
        exact hc.candidate_terminal_connected hx hvalid hnext hend hcan
      · contradiction
  · contradiction

end Meanders.FirstCrossing
