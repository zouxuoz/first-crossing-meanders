import Meanders.Core.Word.Balanced

/-!
# Heights and partners under word splices

A prefix adds a constant to every later height. These lemmas let active boundary
proofs describe a splice by its local height change, without re-expanding
letter counts in each transition case.
-/

namespace Meanders

open DyckStep

variable {a b w : List DyckStep} {i l r : ℕ}

theorem height_cons (s : DyckStep) (w : List DyckStep) (i : ℕ) :
    height (s :: w) (i + 1) = stepHeight s + height w i := by
  cases s <;> simp [height, stepHeight] <;> omega

theorem height_append (a b : List DyckStep) (i : ℕ) :
    height (a ++ b) i = height a i + height b (i - a.length) := by
  simp only [height, List.take_append, List.count_append, Nat.cast_add]
  ring

theorem height_append_left (hi : i ≤ a.length) : height (a ++ b) i = height a i := by
  rw [height_append, Nat.sub_eq_zero_of_le hi, height_zero, add_zero]

theorem height_append_right (a b : List DyckStep) (i : ℕ) :
    height (a ++ b) (a.length + i) = height a a.length + height b i := by
  rw [height_append, Nat.add_sub_cancel_left, height_of_length_le (by omega)]

/-- A zero final height and nonnegative prefixes characterize balanced words. -/
theorem balanced_iff_height (w : List DyckStep) :
    Balanced w ↔ height w w.length = 0 ∧ ∀ i, 0 ≤ height w i := by
  rw [balanced_iff]
  simp only [height, List.take_length]
  constructor
  · rintro ⟨he, hp⟩
    exact ⟨by omega, fun i => by have := hp i; omega⟩
  · rintro ⟨he, hp⟩
    exact ⟨by omega, fun i => by have := hp i; omega⟩

/-- Appending a word does not change pairs wholly inside the prefix. -/
theorem paired_append_left (hr : r < a.length) :
    Paired (a ++ b) l r ↔ Paired a l r := by
  unfold Paired
  rw [height_append_left (by omega : r + 1 ≤ a.length)]
  by_cases hl : l ≤ r
  · rw [height_append_left (by omega : l ≤ a.length)]
    have hh : ∀ j, j < r → height (a ++ b) (j + 1) = height a (j + 1) :=
      fun j hj => height_append_left (by omega)
    constructor
    · rintro ⟨-, hlr, he, hp⟩
      exact ⟨hr, hlr, he, fun j hj hlj => by rw [← hh j hj]; exact hp j hj hlj⟩
    · rintro ⟨-, hlr, he, hp⟩
      exact ⟨by simp only [List.length_append]; omega, hlr, he,
        fun j hj hlj => by rw [hh j hj]; exact hp j hj hlj⟩
  · have hnl : ¬ l < r := by omega
    simp [hnl]

/-- Prefixing a word shifts both partner indices by the prefix length. -/
theorem paired_append_right (a b : List DyckStep) (l r : ℕ) :
    Paired (a ++ b) (a.length + l) (a.length + r) ↔ Paired b l r := by
  unfold Paired
  rw [show a.length + r + 1 = a.length + (r + 1) by omega,
    height_append_right, height_append_right]
  simp only [List.length_append, Nat.add_lt_add_iff_left, add_right_inj]
  constructor
  · rintro ⟨hr, hlr, he, hp⟩
    refine ⟨hr, hlr, he, fun j hj hlj => ?_⟩
    have hh := hp (a.length + j) (by omega) (by omega)
    rw [show a.length + j + 1 = a.length + (j + 1) by omega, height_append_right] at hh
    omega
  · rintro ⟨hr, hlr, he, hp⟩
    refine ⟨hr, hlr, he, fun j hj hlj => ?_⟩
    have hjlen : a.length ≤ j := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hjlen
    rw [show a.length + k + 1 = a.length + (k + 1) by omega, height_append_right]
    have hh := hp k (by omega) (by omega)
    omega

/-- Conversely, the interior of a displayed matched pair is balanced. -/
theorem balanced_of_paired_around (a b c : List DyckStep)
    (h : Paired (a ++ U :: c ++ D :: b) a.length (a.length + c.length + 1)) :
    Balanced c := by
  have hp : Paired (U :: c ++ D :: b) 0 (c.length + 1) := by
    apply (paired_append_right a (U :: c ++ D :: b) 0 (c.length + 1)).mp
    simpa [List.append_assoc, Nat.add_assoc] using h
  have he := hp.height_eq
  rw [List.cons_append, height_zero, height_cons, height_append_right c (D :: b) 1] at he
  have hz : height c c.length = 0 := by simpa [height, stepHeight] using he
  apply (balanced_iff_height c).mpr
  refine ⟨hz, fun i => ?_⟩
  by_cases hi : i ≤ c.length
  · have hlt := hp.height_lt (j := i + 1) (by omega) (by omega)
    rw [List.cons_append, height_zero, height_cons, height_append_left hi] at hlt
    change 0 < 1 + height c i at hlt
    omega
  · rw [height_of_length_le (by omega), hz]

/-- Splitting at a letter keeps its position explicit. -/
theorem split_at_letter {s : DyckStep} (h : w[i]? = some s) :
    ∃ a b, a.length = i ∧ w = a ++ s :: b := by
  obtain ⟨hi, hs⟩ := List.getElem?_eq_some_iff.mp h
  refine ⟨w.take i, w.drop (i + 1), by simp [Nat.min_eq_left hi.le], ?_⟩
  rw [← hs, ← List.drop_eq_getElem_cons hi, List.take_append_drop]

/-- A paired interval can be read as an exact balanced-delimiter split. -/
theorem Paired.split (h : Paired w l r) :
    ∃ a b c, a.length = l ∧ a.length + c.length + 1 = r ∧
      w = a ++ U :: c ++ D :: b ∧ Balanced c := by
  obtain ⟨a, rest, hal, hw⟩ := split_at_letter h.isU
  have hdr : rest[r - (l + 1)]? = some D := by
    have hd := h.isD
    rw [hw, List.getElem?_append_right (by have := h.lt; omega), hal,
      show r - l = (r - (l + 1)) + 1 by have := h.lt; omega,
      List.getElem?_cons_succ] at hd
    exact hd
  obtain ⟨c, b, hcr, hrest⟩ := split_at_letter hdr
  have hr : a.length + c.length + 1 = r := by have := h.lt; omega
  have hword : w = a ++ U :: c ++ D :: b := by rw [hw, hrest]; simp
  refine ⟨a, b, c, hal, hr, hword, ?_⟩
  apply balanced_of_paired_around a b c
  have hp : Paired w a.length (a.length + c.length + 1) := by rwa [hr, hal]
  rwa [hword] at hp

/-- Replace a block by another of the same net height, without dipping below
both of its boundary heights. This covers the local active boundary surgeries. -/
theorem Balanced.replace {a b c d : List DyckStep} (h : Balanced (a ++ b ++ d))
    (he : height c c.length = height b b.length)
    (hc : ∀ i, min 0 (height b b.length) ≤ height c i) : Balanced (a ++ c ++ d) := by
  have tail (w : List DyckStep) (k : ℕ) :
      height (a ++ w ++ d) (a.length + w.length + k) =
        height a a.length + height w w.length + height d k := by
    rw [← List.length_append, height_append_right, List.length_append, height_append_right]
  have ha : 0 ≤ height a a.length := by
    have hh := h.height_nonneg a.length
    rwa [List.append_assoc, height_append_left le_rfl] at hh
  have hb : 0 ≤ height a a.length + height b b.length := by
    have hh := h.height_nonneg (a.length + b.length)
    rw [show a.length + b.length = a.length + b.length + 0 by omega, tail] at hh
    simpa using hh
  apply (balanced_iff_height _).mpr
  constructor
  · have hz := h.height_length
    simp only [List.length_append] at hz ⊢
    rw [tail, he, ← tail b d.length]
    exact hz
  · intro i
    by_cases hi : i ≤ a.length
    · rw [List.append_assoc, height_append_left hi]
      have hh := h.height_nonneg i
      rwa [List.append_assoc, height_append_left hi] at hh
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show a.length ≤ i by omega)
    by_cases hj : j ≤ c.length
    · rw [List.append_assoc, height_append_right, height_append_left hj]
      have hh := hc j
      rcases le_total (height b b.length) 0 with hb0 | hb0
      · rw [min_eq_right hb0] at hh
        omega
      · rw [min_eq_left hb0] at hh
        omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show c.length ≤ j by omega)
    rw [← Nat.add_assoc, tail, he, ← tail b k]
    exact h.height_nonneg _

/-- Old positions shift by two at an inserted adjacent pair. -/
def insertPairIndex (cut i : ℕ) : ℕ := if i < cut then i else i + 2

end Meanders
