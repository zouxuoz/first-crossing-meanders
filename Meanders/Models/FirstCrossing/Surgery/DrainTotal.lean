import Meanders.Models.FirstCrossing.Surgery.Drain
import Meanders.Models.FirstCrossing.Surgery.CyclicSplice

/-! FIFO drain totality from the actual adjacent cyclic splice theorem. -/

namespace Meanders.FirstCrossing

/-- Removing two distinct FIFO heads filters precisely those names from every group. -/
theorem Ports.popHeads_get_filter {p : Ports} (hn : p.flat.Nodup)
    {left right : Group} (hd : left ≠ right) {x y : ℕ} {xs ys : List ℕ}
    (hl : p.get left = x :: xs) (hr : p.get right = y :: ys) (g : Group) :
    (p.popHeads left right).get g = (p.get g).filter (fun i => i != x && i != y) := by
  have hf : ((p.popHeads left right).get g).filter (fun i => i != x && i != y) =
      (p.popHeads left right).get g := by
    apply List.filter_eq_self.mpr
    intro i hi
    have hmem := (Ports.popHeads_mem hn hd hl hr).mp
      ((Ports.mem_flat_iff _ _).mpr ⟨g, hi⟩)
    simp [hmem.2.1, hmem.2.2]
  by_cases hgl : g = left
  · subst g
    simpa [Ports.popHeads_get p hd, hl] using hf.symm
  by_cases hgr : g = right
  · subst g
    simpa [Ports.popHeads_get p hd, hr, Ne.symm hd] using hf.symm
  simpa [Ports.popHeads_get p hd, hgl, hgr] using hf.symm

/-- The cyclic order after dropping FIFO heads is the original order with exactly
those two names removed; reversals of the left-upper/right-lower groups commute. -/
theorem Ports.popHeads_cyclic {p : Ports} (hn : p.flat.Nodup)
    {left right : Group} (hd : left ≠ right) {x y : ℕ} {xs ys : List ℕ}
    (hl : p.get left = x :: xs) (hr : p.get right = y :: ys) :
    (p.popHeads left right).cyclic = p.cyclic.filter (fun i => i != x && i != y) := by
  change ((p.popHeads left right).get .pl).reverse ++
      (p.popHeads left right).get .pr ++ ((p.popHeads left right).get .qr).reverse ++
      (p.popHeads left right).get .ql = _
  rw [Ports.popHeads_get_filter hn hd hl hr .pl,
    Ports.popHeads_get_filter hn hd hl hr .pr,
    Ports.popHeads_get_filter hn hd hl hr .qr,
    Ports.popHeads_get_filter hn hd hl hr .ql]
  simp [Ports.cyclic, Ports.get, List.filter_append, List.filter_reverse]

/-- A one-edge drain at a physical FIFO seam succeeds without assuming its output check. -/
theorem drain_one_total_of_seam {w : Splice} {left right : Group}
    (hd : left ≠ right) (hn : w.ports.flat.Nodup) (hm : MateInvariant w.mate)
    (hc : CoversLive w) (hcheck : cyclicCheck w.mate w.ports.cyclic [] = true)
    {x y : ℕ} {xs ys : List ℕ} (hl : w.ports.get left = x :: xs)
    (hr : w.ports.get right = y :: ys)
    (hseam : AtSeam w.ports.cyclic x y ∨ AtSeam w.ports.cyclic y x) :
    ∃ out, drain 1 left right w = some out := by
  obtain ⟨a, hx⟩ := (hc x).mp ((Ports.mem_flat_iff _ _).mpr ⟨left, by simp [hl]⟩)
  obtain ⟨b, hy⟩ := (hc y).mp ((Ports.mem_flat_iff _ _).mpr ⟨right, by simp [hr]⟩)
  obtain ⟨out, hj, -, -, -, -, hports⟩ :=
    spliceJoin_spec (w := {w with ports := w.ports.popHeads left right})
      hm hx hy (Ports.heads_ne hn hd hl hr)
  have hncyc : w.ports.cyclic.Nodup := (w.ports.cyclic_perm_flat.nodup_iff).mpr hn
  have hccyc : ∀ i, i ∈ w.ports.cyclic ↔ Live w.mate i :=
    fun i => w.ports.cyclic_perm_flat.mem_iff.trans (hc i)
  have hvalid := spliceJoin_cyclicCheck_adjacent
    (w := {w with ports := w.ports.popHeads left right}) hncyc hm hccyc hcheck hseam hj
  have hfinal : cyclicCheck out.mate out.ports.cyclic [] = true := by
    rw [hports, Ports.popHeads_cyclic hn hd hl hr]
    exact hvalid
  refine ⟨out, ?_⟩
  rw [drain_one_eq hl hr, hj]
  simp [hfinal]

/-- Upper-owner FIFO draining succeeds at its actual oldest endpoints. -/
theorem drain_one_total_upper {w : Splice} (hn : w.ports.flat.Nodup)
    (hm : MateInvariant w.mate) (hc : CoversLive w)
    (hcheck : cyclicCheck w.mate w.ports.cyclic [] = true)
    {x y : ℕ} {xs ys : List ℕ} (hl : w.ports.pl = x :: xs)
    (hr : w.ports.pr = y :: ys) : ∃ out, drain 1 .pl .pr w = some out := by
  exact drain_one_total_of_seam (by decide) hn hm hc hcheck hl hr
    (Or.inl (w.ports.upper_fifo_seam hl hr))

/-- Lower-owner FIFO draining succeeds despite its reversed physical cyclic orientation. -/
theorem drain_one_total_lower {w : Splice} (hn : w.ports.flat.Nodup)
    (hm : MateInvariant w.mate) (hc : CoversLive w)
    (hcheck : cyclicCheck w.mate w.ports.cyclic [] = true)
    {x y : ℕ} {xs ys : List ℕ} (hl : w.ports.ql = x :: xs)
    (hr : w.ports.qr = y :: ys) : ∃ out, drain 1 .ql .qr w = some out := by
  exact drain_one_total_of_seam (by decide) hn hm hc hcheck hl hr
    (Or.inr (w.ports.lower_fifo_seam hr hl))

end Meanders.FirstCrossing
