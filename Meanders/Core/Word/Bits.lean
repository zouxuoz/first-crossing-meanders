import Meanders.Core.Word.Partner
import Mathlib.Data.Nat.Bitwise

/-!
# Packed words

A word of `DyckStep`s is packed into a natural number: bit `i` is set when
letter `i` is `U`, and a *sentinel* bit at position `w.length` records the
length. So `pack [] = 1`, `pack [U, D] = 0b101`, and every positive number
is the packing of exactly one word (`unpack`). Small numbers are unboxed
scalars at run time, so an evaluator whose state is a packed word never
allocates, and `Nat.log2`, shifts, `|||`, and `^^^` are single machine
operations on them.

The lemmas here are what a bit-level implementation of a word operation
needs: `testBit_pack` characterises every bit, and `Nat.eq_of_testBit_eq`
turns an equation between packed words into a check bit by bit.
-/

namespace Meanders

open DyckStep

/-! ## Packing -/

/-- The packed form of a word: bit `i` is set when letter `i` is `U`, and a
sentinel bit at `w.length` records the length. -/
def pack : List DyckStep → ℕ
  | [] => 1
  | U :: w => 2 * pack w + 1
  | D :: w => 2 * pack w

@[simp] theorem pack_nil : pack [] = 1 := rfl
@[simp] theorem pack_cons_U (w : List DyckStep) : pack (U :: w) = 2 * pack w + 1 := rfl
@[simp] theorem pack_cons_D (w : List DyckStep) : pack (D :: w) = 2 * pack w := rfl

theorem pack_pos (w : List DyckStep) : 0 < pack w := by
  induction w with
  | nil => simp
  | cons s w ih => cases s <;> (simp only [pack]; omega)

theorem pack_lt (w : List DyckStep) : pack w < 2 ^ (w.length + 1) := by
  induction w with
  | nil => simp
  | cons s w ih => cases s <;> simp only [pack, List.length_cons, pow_succ] at ih ⊢ <;> omega

theorem two_pow_length_le_pack (w : List DyckStep) : 2 ^ w.length ≤ pack w := by
  induction w with
  | nil => simp
  | cons s w ih => cases s <;> simp only [pack, List.length_cons, pow_succ] at ih ⊢ <;> omega

/-- The sentinel recovers the length. -/
theorem log2_pack (w : List DyckStep) : (pack w).log2 = w.length := by
  rw [Nat.log2_eq_iff (Nat.pos_iff_ne_zero.1 (pack_pos w))]
  exact ⟨two_pow_length_le_pack w, pack_lt w⟩

/-- Bit `i` of the packed word: the letter at `i` is `U`, or `i` is the sentinel. -/
theorem testBit_pack (w : List DyckStep) (i : ℕ) :
    (pack w).testBit i = (w[i]? == some U || i == w.length) := by
  induction w generalizing i with
  | nil =>
    cases i with
    | zero => simp
    | succ i => simp [Nat.testBit_add_one]
  | cons s w ih =>
    cases i with
    | zero =>
      cases s
      · have : (2 * pack w + 1) % 2 = 1 := by omega
        simp [this]
      · simp
    | succ i =>
      cases s
      · have : (2 * pack w + 1) / 2 = pack w := by omega
        simp [Nat.testBit_add_one, this, ih]
      · have : 2 * pack w / 2 = pack w := by omega
        simp [Nat.testBit_add_one, this, ih]

/-! ## Unpacking -/

/-- The word packed as `k`, for `0 < k`: the bits below the leading one. -/
def unpack (k : ℕ) : List DyckStep :=
  (List.range k.log2).map fun i => if k.testBit i then U else D

@[simp] theorem length_unpack (k : ℕ) : (unpack k).length = k.log2 := by simp [unpack]

theorem getElem?_unpack (k i : ℕ) :
    (unpack k)[i]? = if i < k.log2 then some (if k.testBit i then U else D) else none := by
  by_cases hi : i < k.log2
  · simp [unpack, hi]
  · rw [ite_eq_right hi]
    simp only [unpack, List.getElem?_map]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem unpack_pack (w : List DyckStep) : unpack (pack w) = w := by
  apply List.ext_getElem?
  intro i
  rw [getElem?_unpack, log2_pack, testBit_pack]
  by_cases hi : i < w.length
  · rw [ite_eq_left hi]
    rcases getElem?_eq_U_or_D hi with h | h <;> simp [h, Nat.ne_of_lt hi]
  · rw [ite_eq_right hi, List.getElem?_eq_none (by omega)]

/-- The leading bit of a positive number is set. -/
theorem testBit_log2_self {k : ℕ} (hk : 0 < k) : k.testBit k.log2 = true := by
  have hne : k ≠ 0 := Nat.pos_iff_ne_zero.1 hk
  have h1 : 2 ^ k.log2 ≤ k := Nat.log2_self_le hne
  have h2 : k < 2 ^ (k.log2 + 1) := (Nat.log2_lt hne).1 (Nat.lt_succ_self _)
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have : k / 2 ^ k.log2 = 1 := by
    rw [pow_succ] at h2
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  simp [this]

theorem testBit_of_log2_lt {k i : ℕ} (hi : k.log2 < i) : k.testBit i = false := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · apply Nat.testBit_lt_two_pow
    calc k < 2 ^ (k.log2 + 1) := (Nat.log2_lt (Nat.pos_iff_ne_zero.1 hk)).1 (Nat.lt_succ_self _)
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi

theorem pack_unpack {k : ℕ} (hk : 0 < k) : pack (unpack k) = k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_pack, getElem?_unpack, length_unpack]
  rcases lt_trichotomy i k.log2 with hi | rfl | hi
  · rw [ite_eq_left hi]
    cases k.testBit i <;> simp [Nat.ne_of_lt hi]
  · simp [testBit_log2_self hk]
  · have hni : ¬ i < k.log2 := by omega
    rw [ite_eq_right hni, testBit_of_log2_lt hi]
    simp [Nat.ne_of_gt hi]

/-! ## Bit operations -/

/-- Clear bit `i` of `x`. -/
def clearBit (x i : ℕ) : ℕ := if x.testBit i then x ^^^ 2 ^ i else x

/-- The letters of a packed word, with the sentinel cleared. -/
def body (k : ℕ) : ℕ := clearBit k k.log2

end Meanders
