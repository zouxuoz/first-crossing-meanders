import Meanders.Core.Matching.Dyck
import Mathlib.Data.Finset.Sort

/-!
# Unfinished arches in a matching prefix

Noncrossing arches behave as a stack: when a crossing closes an arch, its
partner is the greatest unfinished opener. These facts describe one side of
an active boundary and do not depend on the other matching or on connectivity.
-/

namespace Meanders.NoncrossingMatching

variable {n t : ℕ} (m : NoncrossingMatching n)

/-- Openers whose partners have not yet been processed. -/
def active (t : ℕ) : Finset (Point n) :=
  Finset.univ.filter fun v => v.val < t ∧ t ≤ m.partner v

@[simp] theorem mem_active {v : Point n} :
    v ∈ m.active t ↔ v.val < t ∧ t ≤ m.partner v := by simp [active]

@[simp] theorem active_zero : m.active 0 = ∅ := by ext v; simp

/-- Whether the newly read crossing opens this matching's arch. -/
def opens (v : Point n) : Prop := v < m.partner v

instance (v : Point n) : Decidable (m.opens v) := inferInstanceAs (Decidable (v < m.partner v))

theorem partner_lt_of_not_opens {v : Point n} (h : ¬ m.opens v) : m.partner v < v :=
  lt_of_le_of_ne (le_of_not_gt h) (m.partner_ne v)

/-- An arch crossing the cut either starts here or survived the previous cut. -/
theorem mem_active_succ {v u : Point n} :
    u ∈ m.active (v.val + 1) ↔
      (u = v ∧ m.opens v) ∨ (u ∈ m.active v.val ∧ m.partner u ≠ v) := by
  simp only [mem_active, opens, Fin.lt_def]
  have hune : m.partner u ≠ u := m.partner_ne u
  have hune' : (m.partner u).val ≠ u.val := fun h => hune (Fin.ext h)
  constructor
  · rintro ⟨hu, hp⟩
    by_cases huv : u = v
    · subst u
      exact Or.inl ⟨rfl, by omega⟩
    · have hval : u.val ≠ v.val := fun h => huv (Fin.ext h)
      exact Or.inr ⟨⟨by omega, by omega⟩, fun h => by rw [h] at hp; omega⟩
  · rintro (⟨rfl, hp⟩ | ⟨⟨hu, hp⟩, hne⟩)
    · exact ⟨by omega, by omega⟩
    · have hval : (m.partner u).val ≠ v.val := fun h => hne (Fin.ext h)
      exact ⟨by omega, by omega⟩

/-- The partner of a closing crossing is an active opener. -/
theorem partner_mem_active {v : Point n} (h : ¬ m.opens v) :
    m.partner v ∈ m.active v.val := by
  rw [mem_active, m.partner_partner]
  exact ⟨m.partner_lt_of_not_opens h, le_rfl⟩

/-- Noncrossing forces a closing arch to consume the top of the opener stack. -/
theorem active_le_partner {v u : Point n} (hu : u ∈ m.active v.val) :
    u ≤ m.partner v := by
  obtain ⟨hut, hpu⟩ := (mem_active m).mp hu
  by_contra hle
  have hpvu : m.partner v < u := lt_of_not_ge hle
  have hpune : m.partner u ≠ v := by
    intro he
    have : u = m.partner v := by rw [← he, m.partner_partner]
    exact (ne_of_gt hpvu) this
  have hvpu : v < m.partner u := lt_of_le_of_ne hpu hpune.symm
  exact m.not_interleave (m.partner_partner v) rfl hpvu hut hvpu

/-- Opening adds the new maximum to the active set. -/
theorem active_succ_open {v : Point n} (h : m.opens v) :
    m.active (v.val + 1) = insert v (m.active v.val) := by
  ext u
  rw [mem_active_succ, Finset.mem_insert]
  constructor
  · rintro (⟨rfl, -⟩ | ⟨hu, -⟩)
    · exact Or.inl rfl
    · exact Or.inr hu
  · rintro (rfl | hu)
    · exact Or.inl ⟨rfl, h⟩
    · refine Or.inr ⟨hu, fun hp => ?_⟩
      have he : u = m.partner v := by rw [← hp, m.partner_partner]
      have hut := ((mem_active m).mp hu).1
      rw [he] at hut
      exact (not_lt_of_ge h.le) hut

/-- Closing removes precisely the matching opener. -/
theorem active_succ_close {v : Point n} (h : ¬ m.opens v) :
    m.active (v.val + 1) = (m.active v.val).erase (m.partner v) := by
  ext u
  rw [mem_active_succ, Finset.mem_erase]
  have he : m.partner u = v ↔ u = m.partner v := by
    constructor
    · intro hp; rw [← hp, m.partner_partner]
    · rintro rfl; exact m.partner_partner v
  simp [h, he, and_comm]

/-- The active width is exactly the Dyck height at the scan cut. -/
theorem card_active (ht : t ≤ 2 * n) : (m.active t).card = height m.wordOf t := by
  induction t with
  | zero => simp [height]
  | succ t ih =>
    let v : Point n := ⟨t, by omega⟩
    have hv : v.val = t := rfl
    have hnot : v ∉ m.active t := by simp [mem_active, hv]
    rw [height_succ, m.step_wordOf (by omega)]
    by_cases ho : m.opens v
    · have ha := m.active_succ_open ho
      rw [hv] at ha
      rw [ha, Finset.card_insert_of_notMem hnot, Nat.cast_add, ih (by omega)]
      have hopen : t < m.partnerIndex t := by
        rw [m.partnerIndex_eq (i := t) (by omega)]
        exact ho
      simp [endpointSign, hopen]
    · have ha := m.active_succ_close ho
      have hmem := m.partner_mem_active ho
      rw [hv] at ha hmem
      rw [ha]
      have hcard := Finset.card_erase_add_one hmem
      have hi := ih (by omega)
      have hclose : ¬ t < m.partnerIndex t := by
        rw [m.partnerIndex_eq (i := t) (by omega)]
        exact ho
      simp only [endpointSign, ite_eq_right hclose]
      omega

/-- Active openers from greatest to least, with the stack top first. -/
def activeList (t : ℕ) : List (Point n) := (m.active t).sort (· ≥ ·)

@[simp] theorem mem_activeList {v : Point n} : v ∈ m.activeList t ↔ v ∈ m.active t := by
  simp [activeList]

@[simp] theorem length_activeList : (m.activeList t).length = (m.active t).card := by
  simp [activeList]

@[simp] theorem activeList_zero : m.activeList 0 = [] := by simp [activeList]

/-- Opening pushes the new crossing onto the opener stack. -/
theorem activeList_succ_open {v : Point n} (h : m.opens v) :
    m.activeList (v.val + 1) = v :: m.activeList v.val := by
  unfold activeList
  rw [m.active_succ_open h]
  apply Finset.sort_insert
  · intro u hu
    exact ((m.mem_active.mp hu).1).le
  · simp

/-- Closing pops the matching opener off the stack. -/
theorem activeList_succ_close {v : Point n} (h : ¬ m.opens v) :
    m.activeList v.val = m.partner v :: m.activeList (v.val + 1) := by
  have hmem := m.partner_mem_active h
  have he : m.active v.val = insert (m.partner v) (m.active (v.val + 1)) := by
    rw [m.active_succ_close h, Finset.insert_erase hmem]
  change (m.active v.val).sort (· ≥ ·) = _
  rw [he]
  apply Finset.sort_insert
  · intro u hu
    apply m.active_le_partner
    rw [m.active_succ_close h] at hu
    exact Finset.mem_of_mem_erase hu
  · rw [m.active_succ_close h]
    exact Finset.notMem_erase _ _

/-- After the final crossing no arch remains unfinished. -/
theorem active_eq_empty (ht : 2 * n ≤ t) : m.active t = ∅ := by
  ext u
  simp only [mem_active, Finset.notMem_empty, iff_false, not_and]
  intro _ hp
  have hh := (m.partner u).isLt
  omega

end Meanders.NoncrossingMatching
