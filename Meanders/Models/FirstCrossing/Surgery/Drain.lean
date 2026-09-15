import Meanders.Models.FirstCrossing.Surgery.Normalize
import Meanders.Models.FirstCrossing.Surgery.Coverage

/-!
# Actual zero-or-one FIFO drains

Per-owner emitted minima increase by at most one during a physical step. These
lemmas therefore cover both drain counts used by the actual recurrence without
introducing a second transition program or a general drain framework.
-/

namespace Meanders.FirstCrossing

/-- Reading a modified group changes exactly that group. -/
theorem Ports.get_set (p : Ports) (g h : Group) (xs : List ℕ) :
    (p.set g xs).get h = if h = g then xs else p.get h := by
  cases g <;> cases h <;> rfl

/-- Every group is a sublist of the fixed storage-order flattening. -/
theorem Ports.get_sublist_flat (p : Ports) (g : Group) : (p.get g).Sublist p.flat := by
  cases g <;> simp only [Ports.get, Ports.flat, List.append_assoc]
  · exact List.sublist_append_left _ _
  · exact (List.sublist_append_left _ _).trans (List.sublist_append_right _ _)
  · exact (List.sublist_append_left _ _).trans
      ((List.sublist_append_right _ _).trans (List.sublist_append_right _ _))
  · exact (List.sublist_append_right _ _).trans
      ((List.sublist_append_right _ _).trans (List.sublist_append_right _ _))

/-- Membership in the flattening means membership in one of the four groups. -/
theorem Ports.mem_flat_iff (p : Ports) (x : ℕ) : x ∈ p.flat ↔ ∃ g, x ∈ p.get g := by
  simp only [Ports.flat, List.mem_append, or_assoc]
  constructor
  · rintro (h | h | h | h)
    · exact ⟨.pl, h⟩
    · exact ⟨.pr, h⟩
    · exact ⟨.ql, h⟩
    · exact ⟨.qr, h⟩
  · rintro ⟨g, hg⟩
    cases g <;> simp_all [Ports.get]

/-- Different groups cannot contain the same live name in a distinct frontier. -/
theorem Ports.group_of_mem {p : Ports} (hn : p.flat.Nodup) {g h : Group} {x : ℕ}
    (hg : x ∈ p.get g) (hh : x ∈ p.get h) : g = h := by
  cases g <;> cases h <;>
    simp_all [Ports.get, Ports.flat, List.nodup_append]
  all_goals aesop

/-- Removing a sublist from one group removes a sublist from storage order. -/
theorem Ports.set_sublist_flat (p : Ports) (g : Group) (xs : List ℕ)
    (h : xs.Sublist (p.get g)) : (p.set g xs).flat.Sublist p.flat := by
  cases g <;> simp only [Ports.get, Ports.set, Ports.flat, List.append_assoc] at *
  · exact h.append_right _
  · exact (h.append_right _).append_left _
  · exact ((h.append_right _).append_left _).append_left _
  · exact ((h.append_left _).append_left _).append_left _

/-- The purely structural result of removing the two original FIFO heads. -/
def Ports.popHeads (p : Ports) (left right : Group) : Ports :=
  (p.set left (p.get left).tail).set right (p.get right).tail

/-- Exactly the selected two groups lose their oldest endpoint. -/
theorem Ports.popHeads_get (p : Ports) {left right : Group} (h : left ≠ right) (g : Group) :
    (p.popHeads left right).get g =
      if g = left then (p.get left).tail
      else if g = right then (p.get right).tail else p.get g := by
  simp only [Ports.popHeads, Ports.get_set]
  by_cases hl : g = left <;> by_cases hr : g = right <;> simp_all

/-- Removing FIFO heads never reorders or duplicates surviving names. -/
theorem Ports.popHeads_sublist (p : Ports) {left right : Group} (h : left ≠ right) :
    (p.popHeads left right).flat.Sublist p.flat := by
  have hfirst := p.set_sublist_flat left (p.get left).tail (List.tail_sublist _)
  have hright : (p.set left (p.get left).tail).get right = p.get right := by
    simp [Ports.get_set, Ne.symm h]
  have hsecond := (p.set left (p.get left).tail).set_sublist_flat right
    (p.get right).tail (by rw [hright]; exact List.tail_sublist _)
  exact hsecond.trans hfirst

/-- The two selected head names are different. -/
theorem Ports.heads_ne {p : Ports} (hn : p.flat.Nodup) {left right : Group}
    (h : left ≠ right) {x y : ℕ} {xs ys : List ℕ}
    (hl : p.get left = x :: xs) (hr : p.get right = y :: ys) : x ≠ y := by
  intro hxy
  subst y
  exact h (Ports.group_of_mem hn (x := x) (by simp [hl]) (by simp [hr]))

/-- Exact group coverage after the two oldest names are removed. -/
theorem Ports.popHeads_mem {p : Ports} (hn : p.flat.Nodup) {left right : Group}
    (h : left ≠ right) {x y i : ℕ} {xs ys : List ℕ}
    (hl : p.get left = x :: xs) (hr : p.get right = y :: ys) :
    i ∈ (p.popHeads left right).flat ↔ i ∈ p.flat ∧ i ≠ x ∧ i ≠ y := by
  have hsub := p.popHeads_sublist h
  have hnleft := (p.get_sublist_flat left).nodup hn
  have hnright := (p.get_sublist_flat right).nodup hn
  rw [hl, List.nodup_cons] at hnleft
  rw [hr, List.nodup_cons] at hnright
  constructor
  · intro hi
    obtain ⟨g, hg⟩ := (Ports.mem_flat_iff _ _).mp hi
    have hgOld : i ∈ p.get g := by
      rw [p.popHeads_get h] at hg
      split at hg
      · rename_i he
        subst g
        exact List.mem_of_mem_tail hg
      · split at hg
        · rename_i he
          subst g
          exact List.mem_of_mem_tail hg
        · exact hg
    refine ⟨hsub.subset hi, ?_, ?_⟩
    · intro he
      subst i
      have hgl : g = left := Ports.group_of_mem hn hgOld (by simp [hl])
      subst g
      have : x ∈ xs := by simpa [p.popHeads_get h, hl] using hg
      exact hnleft.1 this
    · intro he
      subst i
      have hgr : g = right := Ports.group_of_mem hn hgOld (by simp [hr])
      subst g
      have : y ∈ ys := by simpa [p.popHeads_get h, hr, Ne.symm h] using hg
      exact hnright.1 this
  · rintro ⟨hi, hix, hiy⟩
    obtain ⟨g, hg⟩ := (Ports.mem_flat_iff _ _).mp hi
    apply (Ports.mem_flat_iff _ _).mpr
    refine ⟨g, ?_⟩
    rw [p.popHeads_get h]
    split
    · rename_i he
      subst g
      simpa [hl, hix, eq_comm] using hg
    · split
      · rename_i he
        subst g
        simpa [hr, hiy, eq_comm] using hg
      · exact hg

/-- Zero drains preserve the actual scratch state exactly. -/
@[simp] theorem drain_zero (w : Splice) (left right : Group) : drain 0 left right w = some w := rfl

/-- Expose one actual drain at its original two FIFO heads. -/
theorem drain_one_eq {w : Splice} {left right : Group} {x y : ℕ} {xs ys : List ℕ}
    (hl : w.ports.get left = x :: xs) (hr : w.ports.get right = y :: ys) :
    drain 1 left right w =
      (spliceJoin { w with ports := w.ports.popHeads left right } x y).bind fun out =>
        if cyclicCheck out.mate out.ports.cyclic [] then some out else none := by
  simp only [drain, hl, hr, Ports.popHeads, List.head?_cons, List.tail_cons,
    Option.bind_some, Option.bind_eq_bind]
  congr 1
  funext out
  cases cyclicCheck out.mate out.ports.cyclic [] <;> rfl

/-- A successful drain exposes its original heads and one actual successful join. -/
theorem drain_one_success {w out : Splice} {left right : Group}
    (h : drain 1 left right w = some out) :
    ∃ x xs y ys, w.ports.get left = x :: xs ∧ w.ports.get right = y :: ys ∧
      spliceJoin { w with ports := w.ports.popHeads left right } x y = some out := by
  cases hl : w.ports.get left with
  | nil => simp [drain, hl] at h
  | cons x xs =>
    cases hr : w.ports.get right with
    | nil => simp [drain, hl, hr] at h
    | cons y ys =>
      rw [drain_one_eq hl hr] at h
      cases hj : spliceJoin { w with ports := w.ports.popHeads left right } x y with
      | none => simp [hj] at h
      | some z =>
        simp only [hj, Option.bind_some] at h
        split at h
        · cases h
          exact ⟨x, xs, y, ys, rfl, rfl, hj⟩
        · contradiction

/-- Physical FIFO edges determined entirely by the initial oldest-first groups. -/
def fifoEdges (k : ℕ) (p : Ports) (left right : Group) : List (ℕ × ℕ) :=
  (p.get left).take k |>.zip ((p.get right).take k)

/-- Add a fixed list of physical edges to the already processed graph. -/
def addFifoEdges {V : Type*} (G : SimpleGraph V) (port : ℕ → V)
    (edges : List (ℕ × ℕ)) : SimpleGraph V :=
  edges.foldl (fun H e => H ⊔ SimpleGraph.edge (port e.1) (port e.2)) G

/-- One FIFO edge is exactly the pair of original group heads. -/
theorem fifoEdges_one {p : Ports} {left right : Group} {x y : ℕ} {xs ys : List ℕ}
    (hl : p.get left = x :: xs) (hr : p.get right = y :: ys) :
    fifoEdges 1 p left right = [(x, y)] := by simp [fifoEdges, hl, hr]

/-- Successful one-edge draining preserves the actual raw representation and
adds precisely the edge specified by the two original FIFO groups. -/
theorem drain_one_preserves {V : Type*} {w out : Splice} {left right : Group}
    {G : SimpleGraph V} {port : ℕ → V} (hd : left ≠ right)
    (hn : w.ports.flat.Nodup) (hm : MateInvariant w.mate) (hc : CoversLive w)
    (hp : RepresentsLivePaths w.mate G port) (h : drain 1 left right w = some out) :
    out.ports = w.ports.popHeads left right ∧ out.ports.flat.Nodup ∧
      MateInvariant out.mate ∧ CoversLive out ∧ out.mate.length = w.mate.length ∧
      RepresentsLivePaths out.mate (addFifoEdges G port
        (fifoEdges 1 w.ports left right)) port := by
  obtain ⟨x, xs, y, ys, hl, hr, hj⟩ := drain_one_success h
  have hxmem : x ∈ w.ports.flat :=
    (Ports.mem_flat_iff _ _).mpr ⟨left, by simp [hl]⟩
  have hymem : y ∈ w.ports.flat :=
    (Ports.mem_flat_iff _ _).mpr ⟨right, by simp [hr]⟩
  obtain ⟨a, hx⟩ := (hc x).mp hxmem
  obtain ⟨b, hy⟩ := (hc y).mp hymem
  have hxy := Ports.heads_ne hn hd hl hr
  obtain ⟨hmout, hlive, -, hlen, hports⟩ :=
    spliceJoin_result (w := {w with ports := w.ports.popHeads left right}) hm hx hy hxy hj
  refine ⟨hports, ?_, hmout, ?_, hlen, ?_⟩
  · rw [hports]
    exact (w.ports.popHeads_sublist hd).nodup hn
  · intro i
    rw [hports, Ports.popHeads_mem hn hd hl hr, hc i, hlive i]
  · simpa [fifoEdges_one hl hr, addFifoEdges] using
      spliceJoin_represents (w := {w with ports := w.ports.popHeads left right})
        hm hp hx hy hxy hj

/-- Successful draining also retains a witness for every processed component
that no longer has a live frontier endpoint. -/
theorem drain_one_covers {V : Type*} {w out : Splice} {left right : Group}
    {G : SimpleGraph V} {port : ℕ → V} {closed : List V} {processed : V → Prop}
    (hd : left ≠ right) (hn : w.ports.flat.Nodup) (hm : MateInvariant w.mate)
    (hc : CoversLive w) (hp : RepresentsLivePaths w.mate G port)
    (hcover : CoversProcessed w.mate G port closed processed)
    (hcount : closed.length = w.cycles) (h : drain 1 left right w = some out) :
    ∃ closed', CoversProcessed out.mate
      (addFifoEdges G port (fifoEdges 1 w.ports left right)) port closed' processed ∧
      closed'.length = out.cycles := by
  obtain ⟨x, xs, y, ys, hl, hr, hj⟩ := drain_one_success h
  obtain ⟨a, hx⟩ := (hc x).mp ((Ports.mem_flat_iff _ _).mpr ⟨left, by simp [hl]⟩)
  obtain ⟨b, hy⟩ := (hc y).mp ((Ports.mem_flat_iff _ _).mpr ⟨right, by simp [hr]⟩)
  obtain ⟨closed', hcov, hcnt, -⟩ :=
    spliceJoin_covers (w := {w with ports := w.ports.popHeads left right})
      hm hp hcover hcount hx hy (Ports.heads_ne hn hd hl hr) hj
  exact ⟨closed', by simpa [fifoEdges_one hl hr, addFifoEdges] using hcov, hcnt⟩

/-- Both possible physical drain counts preserve the raw path representation,
with groups changed by dropping exactly that many oldest endpoints. -/
theorem drain_small_preserves {V : Type*} {w out : Splice} {left right : Group}
    {G : SimpleGraph V} {port : ℕ → V} {k : ℕ} (hk : k ≤ 1) (hd : left ≠ right)
    (hn : w.ports.flat.Nodup) (hm : MateInvariant w.mate) (hc : CoversLive w)
    (hp : RepresentsLivePaths w.mate G port) (h : drain k left right w = some out) :
    (∀ g, out.ports.get g = if g = left ∨ g = right
      then (w.ports.get g).drop k else w.ports.get g) ∧
      out.ports.flat.Nodup ∧ MateInvariant out.mate ∧ CoversLive out ∧
      out.mate.length = w.mate.length ∧ RepresentsLivePaths out.mate
        (addFifoEdges G port (fifoEdges k w.ports left right)) port := by
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · cases h
    refine ⟨?_, hn, hm, hc, rfl, ?_⟩
    · intro g
      simp
    · simpa [fifoEdges, addFifoEdges] using hp
  · obtain ⟨hports, hnout, hmout, hcout, hlen, hpout⟩ :=
      drain_one_preserves hd hn hm hc hp h
    refine ⟨?_, hnout, hmout, hcout, hlen, hpout⟩
    intro g
    rw [hports, Ports.popHeads_get _ hd]
    by_cases hl : g = left <;> by_cases hr : g = right <;>
      simp_all [List.drop_one]

/-- Closed-component coverage is preserved for either possible physical drain count. -/
theorem drain_small_covers {V : Type*} {w out : Splice} {left right : Group}
    {G : SimpleGraph V} {port : ℕ → V} {closed : List V} {processed : V → Prop}
    {k : ℕ} (hk : k ≤ 1) (hd : left ≠ right) (hn : w.ports.flat.Nodup)
    (hm : MateInvariant w.mate) (hc : CoversLive w)
    (hp : RepresentsLivePaths w.mate G port)
    (hcover : CoversProcessed w.mate G port closed processed)
    (hcount : closed.length = w.cycles) (h : drain k left right w = some out) :
    ∃ closed', CoversProcessed out.mate
      (addFifoEdges G port (fifoEdges k w.ports left right)) port closed' processed ∧
      closed'.length = out.cycles := by
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · cases h
    exact ⟨closed, by simpa [fifoEdges, addFifoEdges] using hcover, hcount⟩
  · exact drain_one_covers hd hn hm hc hp hcover hcount h

end Meanders.FirstCrossing
