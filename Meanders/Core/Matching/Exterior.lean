import Meanders.Core.Matching.Prefix

/-! Exterior arches and the two exposed rays obtained by cutting one. -/

namespace Meanders.NoncrossingMatching

variable {n : ℕ} (m : NoncrossingMatching n)

/-- Arches not strictly enclosed by another arch of the matching. -/
def exteriorArches : Finset (Arch n) :=
  m.arches.filter fun a => ∀ b ∈ m.arches, ¬b.ProperlyEncloses a

@[simp] theorem mem_exteriorArches {a : Arch n} :
    a ∈ m.exteriorArches ↔ a ∈ m.arches ∧ ∀ b ∈ m.arches, ¬b.ProperlyEncloses a := by
  simp [exteriorArches]

/-- Both endpoints of an exterior arch can extend to infinity without crossing an arch. -/
theorem exterior_exposed {a : Arch n} (ha : a ∈ m.exteriorArches)
    {b : Arch n} (hb : b ∈ m.arches) {v : Point n} (hv : a.Contains v) :
    ¬(b.left < v ∧ v < b.right) := by
  obtain ⟨ha, hext⟩ := m.mem_exteriorArches.mp ha
  by_cases hba : b = a
  · subst b; rcases hv with rfl | rfl <;> simp
  · have h := Arch.separated_or_nested (m.disjointEndpoints hb ha hba) (m.not_crosses hb ha)
    have hn := hext b hb
    rcases hv with rfl | rfl <;>
      simp only [Arch.ProperlyEncloses, Fin.lt_def] at h hn ⊢ <;>
      rcases h with h | h | h | h <;> omega

/-- An exterior opener starts with an empty matching stack. -/
theorem mem_exteriorArches_iff_active_empty {a : Arch n} (ha : a ∈ m.arches) :
    a ∈ m.exteriorArches ↔ m.active a.left.val = ∅ := by
  constructor
  · intro hex
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨hu, hup⟩ := m.mem_active.mp hu
    obtain ⟨b, hb, h | h⟩ := m.exists_arch_partner u
    · obtain ⟨hbl, hbr⟩ := h
      have hba : b ≠ a := by intro he; subst b; subst u; omega
      have hd := m.disjointEndpoints hb ha hba
      have he := m.exterior_exposed hex hb a.contains_left
      have hbrne : b.right.val ≠ a.left.val := fun he => hd.2.2.1 (Fin.ext he)
      have hbl' := congrArg Fin.val hbl
      have hbr' := congrArg Fin.val hbr
      simp only [Fin.lt_def] at he
      omega
    · have hbo := b.ordered
      rw [h.1, h.2] at hbo
      simp only [Fin.lt_def] at hbo
      omega
  · intro hempty
    refine m.mem_exteriorArches.mpr ⟨ha, ?_⟩
    intro b hb hencl
    have hmem : b.left ∈ m.active a.left.val := by
      rw [m.mem_active, m.partner_left hb]
      exact ⟨hencl.1, le_of_lt (lt_trans a.ordered hencl.2)⟩
    simp [hempty] at hmem

/-- The crossings that start exterior arches. -/
def exteriorOpeners : Finset (Point n) :=
  Finset.univ.filter fun v => m.opens v ∧ m.active v.val = ∅

@[simp] theorem mem_exteriorOpeners (v : Point n) :
    v ∈ m.exteriorOpeners ↔ m.opens v ∧ m.active v.val = ∅ := by simp [exteriorOpeners]

end Meanders.NoncrossingMatching
