import Meanders.Core.Overlay
import Meanders.Core.Graph.Pairing

/-!
# Cutting one coloured arch

Deleting one arch of the lower matching opens a cycle into a path. It does
not split its component. The argument uses the two perfect matchings: if the
two exposed endpoints were separated, their component would have even size
by its upper pairing, and odd size by its remaining lower pairing.
-/

namespace Meanders

open SimpleGraph

variable {n : ℕ}

/-- Membership in an arch's endpoints is invariant under its matching partner. -/
theorem NoncrossingMatching.partner_contains_iff (m : NoncrossingMatching n) {a : Arch n}
    (ha : a ∈ m.arches) (v : Point n) : a.Contains (m.partner v) ↔ a.Contains v := by
  constructor
  · rintro (h | h)
    · right
      simpa [m.partner_left ha, m.partner_right ha] using congrArg m.partner h
    · left
      simpa [m.partner_left ha, m.partner_right ha] using congrArg m.partner h
  · rintro (rfl | rfl)
    · exact Or.inr (m.partner_left ha)
    · exact Or.inl (m.partner_right ha)

/-- The actual open graph: remove the marked lower arch, retaining all upper edges. -/
def cutGraph (p : NoncrossingMatching n × NoncrossingMatching n) (a : Arch n) : SimpleGraph
    (Point n) where
  Adj u v := p.1.partner u = v ∨
    (p.2.partner u = v ∧ ¬a.Contains u ∧ ¬a.Contains v)
  symm := ⟨by
    intro u v h
    rcases h with h | ⟨h, hu, hv⟩
    · left; rw [← h, p.1.partner_partner]
    · exact Or.inr ⟨by rw [← h, p.2.partner_partner], hv, hu⟩⟩
  loopless := ⟨by
    intro v h
    rcases h with h | ⟨h, -, -⟩
    · exact p.1.partner_ne v h
    · exact p.2.partner_ne v h⟩

instance (p : NoncrossingMatching n × NoncrossingMatching n) (a : Arch n) :
    DecidableRel (cutGraph p a).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

variable (p : NoncrossingMatching n × NoncrossingMatching n) {a : Arch n}

theorem cutGraph_le_unionGraph : cutGraph p a ≤ unionGraph p := by
  intro u v h
  rw [unionGraph_adj]
  exact ⟨(cutGraph p a).ne_of_adj h, h.imp_right And.left⟩

theorem cutGraph_upper (v : Point n) : (cutGraph p a).Adj v (p.1.partner v) := Or.inl rfl

theorem cutGraph_lower (ha : a ∈ p.2.arches) {v : Point n} (hv : ¬a.Contains v) :
    (cutGraph p a).Adj v (p.2.partner v) :=
  Or.inr ⟨rfl, hv, fun h => hv ((p.2.partner_contains_iff ha v).mp h)⟩

/-- The two newly exposed endpoints stay connected after cutting their lower arch. -/
theorem cutGraph_reachable_endpoints (ha : a ∈ p.2.arches) :
    (cutGraph p a).Reachable a.left a.right := by
  classical
  by_contra hsep
  let s : Finset (Point n) := Finset.univ.filter ((cutGraph p a).Reachable a.left)
  have hs (v : Point n) : v ∈ s ↔ (cutGraph p a).Reachable a.left v := by simp [s]
  have hl : a.left ∈ s := (hs _).mpr (Reachable.refl _)
  have hr : a.right ∉ s := by simpa only [hs] using hsep
  have hupper : Even s.card := even_card_of_pairing s p.1.partner
    (fun v hv => (hs _).mpr (((hs _).mp hv).trans (cutGraph_upper p v).reachable))
    (fun v _ => p.1.partner_partner v) (fun v _ => p.1.partner_ne v)
  have hlower : Even (s.erase a.left).card := by
    apply even_card_of_pairing _ p.2.partner
    · intro v hv
      obtain ⟨hvl, hvs⟩ := Finset.mem_erase.mp hv
      have hvr : v ≠ a.right := fun h => hr (h ▸ hvs)
      have hnot : ¬a.Contains v := by simpa [Arch.Contains] using And.intro hvl hvr
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · intro he
        have := congrArg p.2.partner he
        rw [p.2.partner_partner, p.2.partner_left ha] at this
        exact hvr this
      · exact (hs _).mpr (((hs _).mp hvs).trans (cutGraph_lower p ha hnot).reachable)
    · intro v _; exact p.2.partner_partner v
    · intro v _; exact p.2.partner_ne v
  rw [Finset.card_erase_of_mem hl] at hlower
  obtain ⟨i, hi⟩ := hupper
  obtain ⟨j, hj⟩ := hlower
  have := Finset.card_pos.mpr ⟨a.left, hl⟩
  omega

/-- Cutting a coloured arch preserves all component connectivity. -/
theorem cutGraph_reachable_iff (ha : a ∈ p.2.arches) (u v : Point n) :
    (cutGraph p a).Reachable u v ↔ (unionGraph p).Reachable u v := by
  refine ⟨fun h => h.mono (cutGraph_le_unionGraph p), ?_⟩
  have hedge : ∀ u v, (unionGraph p).Adj u v → (cutGraph p a).Reachable u v := by
    intro u v h
    rcases (unionGraph_adj p u v).mp h with ⟨-, hu | hu⟩
    · subst v; exact (cutGraph_upper p u).reachable
    · subst v
      by_cases hc : a.Contains u
      · rcases hc with rfl | rfl
        · rw [p.2.partner_left ha]; exact cutGraph_reachable_endpoints p ha
        · rw [p.2.partner_right ha]; exact (cutGraph_reachable_endpoints p ha).symm
      · exact (cutGraph_lower p ha hc).reachable
  intro h
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Reachable.refl _
  | tail _ hadj ih => exact ih.trans (hedge _ _ hadj)

theorem cutGraph_connected_iff (ha : a ∈ p.2.arches) :
    (cutGraph p a).Connected ↔ (unionGraph p).Connected := by
  constructor
  · intro h; exact h.mono (cutGraph_le_unionGraph p)
  · intro h
    let := h.nonempty
    exact ⟨fun u v => (cutGraph_reachable_iff p ha u v).mpr (h.preconnected u v)⟩

end Meanders
