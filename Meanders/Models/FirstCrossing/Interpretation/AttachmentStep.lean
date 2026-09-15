import Meanders.Models.FirstCrossing.Interpretation.FIFOStep
import Meanders.Models.FirstCrossing.Interpretation.Boundary
import Meanders.Models.FirstCrossing.Surgery.Cup
import Meanders.Models.FirstCrossing.Surgery.Drain

/-! Original source boundary lists under the executable owner attachments. -/

namespace Meanders.FirstCrossing

private theorem map_attached_points {n : ℕ} (g : Group) (xs : List (Point n))
    (ys : List ℕ) (he : ys = xs.map Fin.val) (hb : ∀ i ∈ ys, i < 2 * n) :
    ys.attach.map (fun i => (g.upper, sourcePoint g.side i.val (hb i.val i.property))) =
      xs.map (inwardIncidence g) := by
  subst ys
  rw [List.attach_map, List.map_map]
  conv_rhs => rw [← List.attach_map_val]
  apply List.map_congr_left
  intro a _
  cases g <;> rfl

/-- Physical retained groups are the matching source lists with joined ordinals dropped. -/
theorem Source.retainedGroup_eq_map {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) :
    s.retainedGroup ht g =
      ((sourceOpeningList (s.inwardMatching g) (t.processed g.side)).drop (s.joined t g)).map
        (inwardIncidence g) :=
  map_attached_points g _ _ (s.retainedIndices_eq_map ht g)
    (fun _ hi => s.retainedIndex_lt ht g hi)

private theorem Source.inward_downs {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) :
    downs (s.inwardMatching g).wordOf (t.processed g.side) = (s.counters t).get g := by
  have he := congrArg (fun w : List DyckStep => w.count DyckStep.D) (s.prefix_inward ht g)
  simpa only [Source.counters, Counters.get_ofFn, downs] using he.symm

private theorem Source.joined_le_originalSlack {spec : RunSpec} (s : Source spec)
    (t : Stage) (g : Group) :
    s.joined t g ≤ t.processed g.side - spec.budgets.get g - (s.counters t).get g := by
  cases hs : spec.sector with
  | low => cases g <;> simp [Source.joined, geometry, hs, Counters.zero, Counters.get, Group.other]
  | high L u v =>
    have hh : s.joined t g ≤ (geometry spec t (s.counters t)).emitted.get g := Nat.min_le_left _ _
    rwa [emitted_eq_originalCounters spec t (s.counters t) g hs (s.counter_le_budget t g)] at hh

private theorem Source.joined_le_openings {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (g : Group) :
    s.joined t g ≤ (sourceOpeningList (s.inwardMatching g) (t.processed g.side)).length := by
  have hj := s.joined_le_originalSlack t g
  have hc := s.counter_le_budget t g
  have hlen := sourceOpeningList_length (s.inwardMatching g) (s.progress_le_boundary ht g)
  have hheight := height_eq_original_downs (s.inwardMatching g).wordOf
    (t.processed g.side) (by simpa using s.progress_le_boundary ht g)
  rw [s.inward_downs ht g] at hheight
  omega

private theorem Source.inward_next_letter {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side)) (g : Group)
    (hside : g.side = side) :
    (s.inwardMatching g).wordOf[t.processed g.side]? = (s.word g)[t.processed g.side]? := by
  have hv := s.visit_lt hnext
  rw [s.word_inward]
  simp only [List.getElem?_take, hside, ite_eq_left hv]

private theorem inward_new_incidence {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side)) (g : Group)
    (hside : g.side = side) :
    inwardIncidence g (⟨t.processed g.side, by rw [hside]; exact s.visit_lt_size hnext⟩ :
      Point spec.n) = (g.upper, s.newPoint hnext) := by
  cases g <;> cases side <;> cases hside <;> rfl

/-- Groups on the unvisited side have their exact old physical list before draining. -/
theorem Source.beforeDrainGroup_unvisited {spec : RunSpec} (s : Source spec)
    {t : Stage} (ht : s.Progress t) (side : Side) (g : Group) (hside : side ≠ g.side) :
    s.beforeDrainGroup t side g = s.retainedGroup ht g := by
  rw [s.retainedGroup_eq_map ht, Source.beforeDrainGroup, Stage.processed_next,
    ite_eq_right hside, Nat.add_zero]

/-- An original U appends the fresh owner incidence to the exact pre-drain source group. -/
theorem Source.beforeDrainGroup_U {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (g : Group) (hside : g.side = side)
    (hU : (s.word g)[t.processed g.side]? = some DyckStep.U) :
    s.beforeDrainGroup t side g = s.retainedGroup ht g ++ [(g.upper, s.newPoint hnext)] := by
  let v : Point spec.n := ⟨t.processed g.side, by rw [hside]; exact s.visit_lt_size hnext⟩
  have hstep : (s.inwardMatching g).wordOf[v.val]? = some DyckStep.U :=
    (s.inward_next_letter hnext g hside).trans hU
  have he := source_open_retained (s.inwardMatching g) v hstep (s.joined_le_openings ht g)
  rw [Source.beforeDrainGroup, s.retainedGroup_eq_map ht,
    Stage.processed_next, ite_eq_left hside.symm]
  change (((sourceOpeningList (s.inwardMatching g) (v.val + 1)).drop
    (s.joined t g)).map (inwardIncidence g)) = _
  rw [he, List.map_append, List.map_singleton]
  rw [inward_new_incidence s hnext g hside]

/-- An original D consumes the actual newest owner partner before any FIFO drain. -/
theorem Source.beforeDrainGroup_D {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (g : Group) (hside : g.side = side)
    (hD : (s.word g)[t.processed g.side]? = some DyckStep.D) :
    s.retainedGroup ht g = s.beforeDrainGroup t side g ++
      [(g.upper, (ownerMatching s.matchings g.upper).partner (s.newPoint hnext))] := by
  let v : Point spec.n := ⟨t.processed g.side, by rw [hside]; exact s.visit_lt_size hnext⟩
  have hstep : (s.inwardMatching g).wordOf[v.val]? = some DyckStep.D :=
    (s.inward_next_letter hnext g hside).trans hD
  have hA : downs (s.inwardMatching g).wordOf (v.val + 1) ≤ spec.budgets.get g := by
    rw [downs_succ_of_D hstep]
    change downs (s.inwardMatching g).wordOf (t.processed g.side) + 1 ≤ _
    rw [s.inward_downs ht g]
    have hh := (s.down_original_pos ht g hD).2
    omega
  have hj : s.joined t g ≤ v.val - spec.budgets.get g -
      downs (s.inwardMatching g).wordOf v.val := by
    simpa only [v, s.inward_downs ht g] using s.joined_le_originalSlack t g
  have he := source_close_retained_reverse (s.inwardMatching g) v hstep hA hj
  have hel := congrArg List.reverse he
  simp only [List.reverse_reverse, List.reverse_cons] at hel
  rw [s.retainedGroup_eq_map ht, Source.beforeDrainGroup, Stage.processed_next,
    ite_eq_left hside.symm]
  change ((_ : List (Point spec.n)).map (inwardIncidence g)) =
    ((sourceOpeningList (s.inwardMatching g) (v.val + 1)).drop (s.joined t g)).map _ ++ _
  rw [hel, List.map_append, List.map_singleton]
  have hp := s.inward_partner g v
  have hv := inward_new_incidence s hnext g hside
  apply congrArg (fun z =>
    ((sourceOpeningList (s.inwardMatching g) (v.val + 1)).drop (s.joined t g)).map
      (inwardIncidence g) ++ [z])
  apply Prod.ext
  · rfl
  · rw [hp, congrArg Prod.snd hv]

/-- Exact physical interpretation of the old storage order followed by the new cup. -/
noncomputable def Source.candidateBoundary {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side)) :
    List (Incidence spec.n) :=
  s.retainedBoundary ht ++ [(true, s.newPoint hnext), (false, s.newPoint hnext)]

/-- Total lookup for native temporary names; every live name is inside this boundary. -/
noncomputable def Source.candidatePort {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (i : ℕ) : Incidence spec.n :=
  ((s.candidateBoundary ht hnext)[i]?).getD (true, s.newPoint hnext)

@[simp] theorem Source.candidateBoundary_length {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side)) :
    (s.candidateBoundary ht hnext).length = (s.retainedBoundary ht).length + 2 := by
  simp [Source.candidateBoundary]

/-- The cup's upper name is the first position after the exact old storage boundary. -/
theorem Source.candidatePort_upper {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side)) :
    s.candidatePort ht hnext (s.retainedBoundary ht).length = (true, s.newPoint hnext) := by
  simp [Source.candidatePort, Source.candidateBoundary]

/-- The following cup name is the lower incidence of that same physical crossing. -/
theorem Source.candidatePort_lower {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side)) :
    s.candidatePort ht hnext ((s.retainedBoundary ht).length + 1) =
      (false, s.newPoint hnext) := by
  simp [Source.candidatePort, Source.candidateBoundary]

/-- Fresh cup incidences are absent from the old physical boundary. -/
theorem Source.newIncidence_not_retained {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (owner : Bool) : (owner, s.newPoint hnext) ∉ s.retainedBoundary ht := by
  intro hm
  exact s.newPoint_not_visited hnext (s.retainedBoundary_visited ht hm)

/-- The concrete temporary native names have an injective physical interpretation. -/
theorem Source.candidatePort_injective {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side)) :
    Set.InjOn (s.candidatePort ht hnext) (Set.Iio ((s.retainedBoundary ht).length + 2)) := by
  have hn : (s.candidateBoundary ht hnext).Nodup := by
    rw [Source.candidateBoundary, List.nodup_append']
    refine ⟨s.retainedBoundary_nodup ht, by simp, ?_⟩
    rw [List.disjoint_right]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact s.newIncidence_not_retained ht hnext true
    · exact s.newIncidence_not_retained ht hnext false
  intro i hi j hj he
  have hib : i < (s.candidateBoundary ht hnext).length := by simpa using hi
  have hjb : j < (s.candidateBoundary ht hnext).length := by simpa using hj
  simp only [Source.candidatePort, List.getElem?_eq_getElem hib,
    List.getElem?_eq_getElem hjb, Option.getD_some] at he
  exact hn.getElem_inj.mp he

private theorem map_range_slice {α : Type*} (pre mid post : List α) (default : α) :
    ((List.range mid.length).map (pre.length + ·)).map
      (fun i => ((pre ++ mid ++ post)[i]?).getD default) = mid := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [List.getElem_map, List.getElem_range]
    rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hi₂, List.getElem?_eq_getElem hi₂, Option.getD_some]

/-- Canonical native group names map to precisely the original physical group lists. -/
theorem Source.candidatePort_groups {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side)) (g : Group) :
    ((Ports.ofLengths (geometry spec t (s.counters t)).length).get g).map
      (s.candidatePort ht hnext) = s.retainedGroup ht g := by
  have hpl := s.retainedGroup_length ht .pl
  have hpr := s.retainedGroup_length ht .pr
  have hql := s.retainedGroup_length ht .ql
  have hqr := s.retainedGroup_length ht .qr
  simp only [Counters.get] at hpl hpr hql hqr
  unfold Source.candidatePort Source.candidateBoundary
  let cup := [(true, s.newPoint hnext), (false, s.newPoint hnext)]
  cases g with
  | pl =>
    simpa [Source.retainedBoundary,
      Ports.ofLengths, Ports.get, Counters.get, ← hpl, List.append_assoc, Nat.add_assoc, cup] using
      map_range_slice [] (s.retainedGroup ht .pl)
        (s.retainedGroup ht .pr ++ s.retainedGroup ht .ql ++ s.retainedGroup ht .qr ++ cup)
        (true, s.newPoint hnext)
  | pr =>
    simpa [Source.retainedBoundary,
      Ports.ofLengths, Ports.get, Counters.get, ← hpl, ← hpr,
      List.append_assoc, Nat.add_assoc, cup] using
      map_range_slice (s.retainedGroup ht .pl) (s.retainedGroup ht .pr)
        (s.retainedGroup ht .ql ++ s.retainedGroup ht .qr ++ cup) (true, s.newPoint hnext)
  | ql =>
    simpa [Source.retainedBoundary,
      Ports.ofLengths, Ports.get, Counters.get, ← hpl, ← hpr, ← hql,
      List.append_assoc, Nat.add_assoc, cup] using
      map_range_slice (s.retainedGroup ht .pl ++ s.retainedGroup ht .pr)
        (s.retainedGroup ht .ql) (s.retainedGroup ht .qr ++ cup) (true, s.newPoint hnext)
  | qr =>
    simpa [Source.retainedBoundary,
      Ports.ofLengths, Ports.get, Counters.get, ← hpl, ← hpr, ← hql, ← hqr,
      List.append_assoc, Nat.add_assoc, cup] using
      map_range_slice (s.retainedGroup ht .pl ++ s.retainedGroup ht .pr ++ s.retainedGroup ht .ql)
        (s.retainedGroup ht .qr) cup (true, s.newPoint hnext)

/-- Finishing this visit's FIFO prefix removes exactly its newly shared ordinals. -/
theorem Source.beforeDrainGroup_drop {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side)) (g : Group) :
    (s.beforeDrainGroup t side g).drop (s.joined (t.next side) g - s.joined t g) =
      s.retainedGroup hnext g := by
  rw [Source.beforeDrainGroup, s.retainedGroup_eq_map hnext, ← List.map_drop, List.drop_drop,
    Nat.add_sub_of_le (s.joined_next_between t side g).1]

/-- The executable owner attachment modifies only the selected original stack end. -/
theorem attachOwner_ports {w out : Splice} {g : Group} {down : Bool} {cup : Nat}
    (h : attachOwner w g down cup = some out) :
    out.ports = w.ports.set g
      (if down then (w.ports.get g).dropLast else w.ports.get g ++ [cup]) := by
  cases down with
  | false =>
    simp only [attachOwner, Bool.false_eq_true, ite_false, Option.some.injEq] at h
    subst out
    rfl
  | true =>
    unfold attachOwner at h
    simp only [ite_true] at h ⊢
    cases hr : (w.ports.get g).reverse with
    | nil => simp [hr] at h
    | cons old older =>
      simp only [hr] at h
      have hp := spliceJoin_ports h
      have he := congrArg List.reverse hr
      simp only [List.reverse_reverse, List.reverse_cons] at he
      rw [hp, he, List.dropLast_concat]

/-- The consumed raw D endpoint names the original physical owner partner. -/
theorem Source.attachOwner_D_names {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    (g : Group) (hside : g.side = side)
    (hD : (s.word g)[t.processed g.side]? = some DyckStep.D)
    (port : Nat → Incidence spec.n) (older : List Nat) (old : Nat)
    (hnames : (older ++ [old]).map port = s.retainedGroup ht g) :
    port old = (g.upper, (ownerMatching s.matchings g.upper).partner (s.newPoint hnext)) ∧
      older.map port = s.beforeDrainGroup t side g := by
  rw [s.beforeDrainGroup_D ht hnext g hside hD, List.map_append, List.map_singleton] at hnames
  have hlen := congrArg List.length hnames
  simp only [List.length_append, List.length_map, List.length_singleton,
    Nat.add_right_cancel_iff] at hlen
  have he := List.append_inj hnames (by simpa using hlen)
  exact ⟨by simpa using he.2, he.1⟩

/-- Successful native attachment realizes precisely the source pre-drain physical group. -/
theorem Source.attachOwner_group_map {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    {w out : Splice} (g : Group) (hside : g.side = side) (down : Bool) (cup : Nat)
    (port : Nat → Incidence spec.n)
    (hnames : (w.ports.get g).map port = s.retainedGroup ht g)
    (hcup : port cup = (g.upper, s.newPoint hnext))
    (hletter : (s.word g)[t.processed g.side]? = some (if down then DyckStep.D else DyckStep.U))
    (hattach : attachOwner w g down cup = some out) :
    (out.ports.get g).map port = s.beforeDrainGroup t side g := by
  rw [attachOwner_ports hattach, Ports.get_set, ite_eq_left rfl]
  cases down with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hletter ⊢
    rw [List.map_append, List.map_singleton, hnames, hcup,
      s.beforeDrainGroup_U ht hnext g hside hletter]
  | true =>
    simp only [ite_true] at hletter ⊢
    rw [List.map_dropLast, hnames, s.beforeDrainGroup_D ht hnext g hside hletter,
      List.dropLast_concat]

/-- Every other native group is literally unchanged by this owner attachment. -/
theorem attachOwner_other_ports {w out : Splice} {g other : Group} {down : Bool} {cup : Nat}
    (hne : other ≠ g) (hattach : attachOwner w g down cup = some out) :
    out.ports.get other = w.ports.get other := by
  rw [attachOwner_ports hattach, Ports.get_set, ite_eq_right hne]

/-- Both actual owner attachments produce all four exact original pre-FIFO groups. -/
theorem Source.attachOwners_groups_map {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (ht : s.Progress t) (hnext : s.Progress (t.next side))
    {w upper out : Splice} (upperCup lowerCup : Nat) (port : Nat → Incidence spec.n)
    (hnames : ∀ g, (w.ports.get g).map port = s.retainedGroup ht g)
    (huCup : port upperCup = (true, s.newPoint hnext))
    (hlCup : port lowerCup = (false, s.newPoint hnext))
    (hu : attachOwner w (Group.onSide true side) (s.nextMove t side).upperDown upperCup =
      some upper)
    (hl : attachOwner upper (Group.onSide false side) (s.nextMove t side).lowerDown lowerCup =
      some out) :
    ∀ g, (out.ports.get g).map port = s.beforeDrainGroup t side g := by
  have hside (owner : Bool) : (Group.onSide owner side).side = side := by
    cases owner <;> cases side <;> rfl
  have howner (owner : Bool) : (Group.onSide owner side).upper = owner := by
    cases owner <;> cases side <;> rfl
  have hne : Group.onSide true side ≠ Group.onSide false side := by
    cases side <;> decide
  have huMap := s.attachOwner_group_map ht hnext (Group.onSide true side) (hside true)
    (s.nextMove t side).upperDown upperCup port (hnames _)
    (by simpa only [howner] using huCup)
    (by simpa only [hside] using (s.nextMove_letters hnext).1) hu
  have hlBefore : (upper.ports.get (Group.onSide false side)).map port =
      s.retainedGroup ht (Group.onSide false side) := by
    rw [attachOwner_other_ports hne.symm hu]
    exact hnames _
  have hlMap := s.attachOwner_group_map ht hnext (Group.onSide false side) (hside false)
    (s.nextMove t side).lowerDown lowerCup port hlBefore
    (by simpa only [howner] using hlCup)
    (by simpa only [hside] using (s.nextMove_letters hnext).2) hl
  intro g
  by_cases hgu : g = Group.onSide true side
  · subst g
    rw [attachOwner_other_ports hne hl]
    exact huMap
  by_cases hgl : g = Group.onSide false side
  · subst g
    exact hlMap
  rw [attachOwner_other_ports hgl hl, attachOwner_other_ports hgu hu, hnames]
  symm
  apply s.beforeDrainGroup_unvisited ht side g
  cases side <;> cases g <;> simp_all [Group.onSide, Group.side]

/-- A successful zero-or-one native FIFO drain removes exactly its selected heads. -/
theorem drain_small_ports {w out : Splice} {left right : Group} {k : Nat}
    (hk : k ≤ 1) (hne : left ≠ right) (h : drain k left right w = some out) (g : Group) :
    out.ports.get g = (w.ports.get g).drop (if g = left ∨ g = right then k else 0) := by
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · cases h
    split <;> simp
  · obtain ⟨x, xs, y, ys, hl, hr, hj⟩ := drain_one_success h
    rw [spliceJoin_ports hj, Ports.popHeads_get _ hne]
    by_cases hgl : g = left
    · subst g
      simp
    by_cases hgr : g = right
    · subst g
      simp [hgl]
    simp [hgl, hgr]

/-- The two actual P-then-Q FIFO drains recover every next source retained group. -/
theorem Source.drains_groups_map {spec : RunSpec} (s : Source spec)
    {t : Stage} {side : Side} (hnext : s.Progress (t.next side))
    {w upper out : Splice} (port : Nat → Incidence spec.n)
    (hnames : ∀ g, (w.ports.get g).map port = s.beforeDrainGroup t side g)
    (hp : drain (s.joined (t.next side) .pl - s.joined t .pl) .pl .pr w = some upper)
    (hq : drain (s.joined (t.next side) .ql - s.joined t .ql) .ql .qr upper = some out) :
    ∀ g, (out.ports.get g).map port = s.retainedGroup hnext g := by
  intro g
  rw [drain_small_ports (s.joined_next_between t side .ql).2 (by decide) hq,
    drain_small_ports (s.joined_next_between t side .pl).2 (by decide) hp,
    List.map_drop, List.map_drop, hnames]
  have hjp (t : Stage) : s.joined t .pr = s.joined t .pl := by
    simp [Source.joined, Counters.get, Group.other, Nat.min_comm]
  have hjq (t : Stage) : s.joined t .qr = s.joined t .ql := by
    simp [Source.joined, Counters.get, Group.other, Nat.min_comm]
  cases g <;> simp only [reduceCtorEq, true_or, or_true, or_self, ite_true, ite_false,
    List.drop_zero] <;> rw [← s.beforeDrainGroup_drop hnext]
  all_goals simp only [hjp, hjq]

end Meanders.FirstCrossing
