import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Data.List.Nodup
import Mathlib.Order.Interval.Finset.Nat

/-!
# Balanced words, heights, and the pairing rule

A word is a `List DyckStep`; `U` opens and `D` closes. `height w i` is the
excess of `U`s over `D`s in the first `i` letters, so the word is *balanced*
when its height returns to `0` at the end and never goes negative — which is
exactly Mathlib's `DyckWord`.

The point of this file is the relation `Paired w l r`: position `l` is matched
to position `r`. It is *not* defined by a stack algorithm but by the height
rule, which is a first-order condition:

* the height at `l` is restored immediately after `r`, and
* the height stays strictly above that level everywhere in between.

Stating it this way buys three things at once. It is decidable as written, so
`archesOfWord` below is computable. Its uniqueness properties
(`Paired.right_unique`, `Paired.left_unique`) and the noncrossing property
(`Paired.nested_of_lt`) are two-line height arguments. And existence
(`exists_paired_of_U`, `exists_paired_of_D`) is a discrete intermediate-value
argument run by `Nat.find` / `Nat.findGreatest`, needing no induction on the
word.
-/

namespace Meanders

open DyckStep

variable {α : Type} {w : List DyckStep} {i l r : ℕ}

/-- The signed contribution of a single step. -/
def stepHeight : DyckStep → ℤ
  | U => 1
  | D => -1

/-- The height of `w` after `i` steps: `U`s minus `D`s in the first `i`
letters. Positions `i` past the end of `w` repeat the final height. -/
def height (w : List DyckStep) (i : ℕ) : ℤ :=
  ((w.take i).count U : ℤ) - ((w.take i).count D : ℤ)

/-- Every letter is an opening or a closing step. -/
theorem count_U_add_count_D (w : List DyckStep) : w.count U + w.count D = w.length := by
  induction w with
  | nil => simp
  | cons s w ih => cases s <;> simp_all <;> omega

@[simp] theorem height_zero (w : List DyckStep) : height w 0 = 0 := by simp [height]

theorem height_succ (w : List DyckStep) (i : ℕ) :
    height w (i + 1) = height w i + (w[i]?.map stepHeight).getD 0 := by
  simp only [height, List.take_add_one, List.count_append]
  rcases h : w[i]? with _ | s
  · simp
  · cases s <;> simp [stepHeight] <;> ring

theorem height_succ_of_U (h : w[i]? = some U) : height w (i + 1) = height w i + 1 := by
  rw [height_succ, h]; rfl

theorem height_succ_of_D (h : w[i]? = some D) : height w (i + 1) = height w i - 1 := by
  rw [height_succ, h]; simp [stepHeight]; ring

theorem height_succ_of_none (h : w[i]? = none) : height w (i + 1) = height w i := by
  rw [height_succ, h]; simp

theorem height_succ_le (w : List DyckStep) (i : ℕ) : height w (i + 1) ≤ height w i + 1 := by
  rcases hi : w[i]? with _ | s
  · rw [height_succ_of_none hi]; omega
  · cases s
    · rw [height_succ_of_U hi]
    · rw [height_succ_of_D hi]; omega

theorem sub_one_le_height_succ (w : List DyckStep) (i : ℕ) :
    height w i - 1 ≤ height w (i + 1) := by
  rcases hi : w[i]? with _ | s
  · rw [height_succ_of_none hi]; omega
  · cases s
    · rw [height_succ_of_U hi]; omega
    · rw [height_succ_of_D hi]

theorem getElem?_eq_U_or_D (h : i < w.length) : w[i]? = some U ∨ w[i]? = some D := by
  rw [List.getElem?_eq_getElem h]
  rcases (w[i]).dichotomy with h' | h' <;> simp [h']

theorem height_of_length_le (h : w.length ≤ i) : height w i = height w w.length := by
  simp [height, List.take_of_length_le h]

/-- `l` is matched to `r` in `w`: the height returns to its level at `l` exactly
after `r`, and stays strictly higher in between. -/
def Paired (w : List DyckStep) (l r : ℕ) : Prop :=
  r < w.length ∧ l < r ∧ height w (r + 1) = height w l ∧
    ∀ j, j < r → l ≤ j → height w l < height w (j + 1)

instance : Decidable (Paired w l r) := by unfold Paired; infer_instance

namespace Paired

variable {j l' r' l₁ r₁ l₂ r₂ : ℕ}

theorem lt (h : Paired w l r) : l < r := h.2.1
theorem lt_length (h : Paired w l r) : r < w.length := h.1
theorem left_lt_length (h : Paired w l r) : l < w.length := h.lt.trans h.lt_length
theorem height_eq (h : Paired w l r) : height w (r + 1) = height w l := h.2.2.1

/-- Inside a matched pair the height never drops back to its opening level. -/
theorem height_lt (h : Paired w l r) (hj₁ : l < j) (hj₂ : j ≤ r) :
    height w l < height w j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact h.2.2.2 k (by omega) (by omega)

theorem isU (h : Paired w l r) : w[l]? = some U := by
  rcases getElem?_eq_U_or_D h.left_lt_length with hU | hD
  · exact hU
  · exfalso
    have hlr := h.lt
    have h1 : height w l < height w (l + 1) := h.height_lt (by omega) (by omega)
    have h2 := height_succ_of_D hD
    omega

theorem isD (h : Paired w l r) : w[r]? = some D := by
  rcases getElem?_eq_U_or_D h.lt_length with hU | hD
  · exfalso
    have h1 : height w l < height w r := h.height_lt h.lt le_rfl
    have h2 := height_succ_of_U hU
    have h3 := h.height_eq
    omega
  · exact hD

/-- A position is matched to at most one position on its right. -/
theorem right_unique (h : Paired w l r) (h' : Paired w l r') : r = r' := by
  have hl := h.lt
  have hl' := h'.lt
  by_contra hne
  rcases Nat.lt_or_ge r r' with hlt | hge
  · have h1 := h'.height_lt (show l < r + 1 by omega) (show r + 1 ≤ r' by omega)
    have h2 := h.height_eq
    omega
  · have h1 := h.height_lt (show l < r' + 1 by omega) (show r' + 1 ≤ r by omega)
    have h2 := h'.height_eq
    omega

/-- A position is matched to at most one position on its left. -/
theorem left_unique (h : Paired w l r) (h' : Paired w l' r) : l = l' := by
  have hl := h.lt
  have hl' := h'.lt
  by_contra hne
  rcases Nat.lt_or_ge l l' with hlt | hge
  · have h1 := h.height_lt (show l < l' by omega) (show l' ≤ r by omega)
    have h2 := h.height_eq
    have h3 := h'.height_eq
    omega
  · have h1 := h'.height_lt (show l' < l by omega) (show l ≤ r by omega)
    have h2 := h.height_eq
    have h3 := h'.height_eq
    omega

/-- **Matched pairs never cross.** If `l₁ < l₂ < r₁` then the whole pair
`(l₂, r₂)` sits inside `(l₁, r₁)`. -/
theorem nested_of_lt (h₁ : Paired w l₁ r₁) (h₂ : Paired w l₂ r₂)
    (hl : l₁ < l₂) (hlr : l₂ < r₁) : r₂ < r₁ := by
  have hp₂ := h₂.lt
  by_contra hcon
  rcases eq_or_lt_of_le (not_lt.1 hcon) with heq | hlt
  · exact absurd (h₁.left_unique (heq ▸ h₂)) (by omega)
  · have ha := h₁.height_lt hl (show l₂ ≤ r₁ by omega)
    have hb := h₂.height_lt (show l₂ < r₁ + 1 by omega) (show r₁ + 1 ≤ r₂ by omega)
    have hc := h₁.height_eq
    omega

end Paired

/-! ## Existence of partners

Both existence proofs are discrete intermediate-value arguments: a height that
must come back down (resp. up) does so by unit steps, and the *first* (resp.
*last*) time it does is the partner. `Nat.find` and `Nat.findGreatest` supply
the extremal index together with the minimality clause `Paired` needs. -/

/-- A `U` whose level is eventually returned to has a partner: the first
position after which the height comes back down to its opening level. -/
theorem exists_paired_of_U (hl : l < w.length) (hU : w[l]? = some U)
    (hend : height w w.length ≤ height w l) : ∃ r, Paired w l r := by
  have hex : ∃ k, l < k ∧ k ≤ w.length ∧ height w k ≤ height w l :=
    ⟨w.length, hl, le_rfl, hend⟩
  -- `m` is the first index past `l` at which the height is back down to `height w l`.
  obtain ⟨m, ⟨hm1, hm2, hm3⟩, hmin⟩ :
      ∃ m, (l < m ∧ m ≤ w.length ∧ height w m ≤ height w l) ∧
        ∀ k, k < m → ¬(l < k ∧ k ≤ w.length ∧ height w k ≤ height w l) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hstepU := height_succ_of_U hU
  have hne : m ≠ l + 1 := by
    intro hm; rw [hm] at hm3; omega
  refine ⟨m - 1, by omega, by omega, ?_, ?_⟩
  · have hrw : m - 1 + 1 = m := by omega
    have hprev := hmin (m - 1) (by omega)
    have hgt : height w l < height w (m - 1) := by
      rcases Nat.lt_or_ge l (m - 1) with hc | hc
      · by_contra hcon
        exact hprev ⟨hc, by omega, by omega⟩
      · have : m - 1 = l := by omega
        rw [this]; omega
    have hstep := sub_one_le_height_succ w (m - 1)
    rw [hrw] at hstep ⊢
    omega
  · intro j hj hjl
    have hprev := hmin (j + 1) (by omega)
    by_contra hcon
    exact hprev ⟨by omega, by omega, by omega⟩

/-- A `D` whose level was reached before has a partner: the last position at
which the height was at the closing level. -/
theorem exists_paired_of_D (hr : r < w.length) (hD : w[r]? = some D)
    (hstart : 0 ≤ height w (r + 1)) : ∃ l, Paired w l r := by
  -- `l` is the last index at or before `r` whose height is the closing level.
  obtain ⟨l, hl1, hl2, hl3⟩ :
      ∃ l, l ≤ r ∧ height w l ≤ height w (r + 1) ∧
        ∀ k, l < k → k ≤ r → height w (r + 1) < height w k := by
    refine ⟨Nat.findGreatest (fun k => height w k ≤ height w (r + 1)) r,
      Nat.findGreatest_le r,
      Nat.findGreatest_spec (P := fun k => height w k ≤ height w (r + 1)) (Nat.zero_le r)
        (by simpa using hstart), fun k hk1 hk2 => ?_⟩
    have := Nat.findGreatest_is_greatest hk1 hk2
    omega
  have hstepD := height_succ_of_D hD
  have hlr : l < r := by
    rcases eq_or_lt_of_le hl1 with rfl | h
    · omega
    · exact h
  have hkey : height w (r + 1) = height w l := by
    have h1 := hl3 (l + 1) (by omega) (by omega)
    have h2 := height_succ_le w l
    omega
  exact ⟨l, hr, hlr, hkey, fun j hj hjl => by
    have := hl3 (j + 1) (by omega) (by omega); omega⟩

/-! ## Enumerating and recognising balanced words -/

/-- All words of length `k` over `alphabet`, in lexicographic prefix order. -/
def wordsOver (alphabet : List α) : ℕ → List (List α)
  | 0 => [[]]
  | k + 1 => alphabet.flatMap fun a => (wordsOver alphabet k).map (a :: ·)

@[simp] theorem mem_wordsOver {alphabet : List α} (ha : ∀ a : α, a ∈ alphabet)
    {k : ℕ} {w : List α} :
    w ∈ wordsOver alphabet k ↔ w.length = k := by
  induction k generalizing w with
  | zero => simp [wordsOver, List.length_eq_zero_iff]
  | succ k ih =>
    cases w with
    | nil => simp [wordsOver]
    | cons a w => simp [wordsOver, ih, ha]

theorem nodup_wordsOver {alphabet : List α} (halphabet : alphabet.Nodup) (k : ℕ) :
    (wordsOver alphabet k).Nodup := by
  induction k with
  | zero => simp [wordsOver]
  | succ k ih =>
    rw [wordsOver, List.nodup_flatMap]
    refine ⟨fun _ _ => ih.map fun _ _ h => List.tail_eq_of_cons_eq h, ?_⟩
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro _ ⟨_, _, rfl⟩ ⟨_, _, h⟩
    have hne : alphabet[i] ≠ alphabet[j] := fun h' =>
      absurd (halphabet.getElem_inj_iff.1 h') (by omega)
    exact hne (List.head_eq_of_cons_eq h).symm

/-- The balanced-word condition of semilength `n`, as a decidable predicate on
raw words: length `2n`, height back to `0` at the end, height never negative.
`isDyck_iff_dyckWord` records that this is Mathlib's `DyckWord`. -/
def IsDyck (n : ℕ) (w : List DyckStep) : Prop :=
  w.length = 2 * n ∧ height w (2 * n) = 0 ∧ ∀ i, i ≤ 2 * n → 0 ≤ height w i

instance (n : ℕ) (w : List DyckStep) : Decidable (IsDyck n w) := by
  unfold IsDyck; infer_instance

namespace IsDyck

variable {n : ℕ} (h : IsDyck n w)
include h

theorem length : w.length = 2 * n := h.1

theorem height_nonneg (i : ℕ) : 0 ≤ height w i := by
  rcases le_or_gt i (2 * n) with hi | hi
  · exact h.2.2 i hi
  · have hle : w.length ≤ i := by rw [h.1]; omega
    rw [height_of_length_le hle, h.1]
    exact le_of_eq h.2.1.symm

theorem height_length : height w w.length = 0 := by rw [h.length]; exact h.2.1

end IsDyck

/-- Height in terms of counts, the form Mathlib's `DyckWord` axioms are
stated in. -/
theorem height_nonneg_iff (w : List DyckStep) (i : ℕ) :
    0 ≤ height w i ↔ (w.take i).count D ≤ (w.take i).count U := by
  simp [height]

/-- A balanced word of semilength `n`, as a Mathlib `DyckWord`. -/
def IsDyck.toDyckWord {n : ℕ} (h : IsDyck n w) : DyckWord where
  toList := w
  count_U_eq_count_D := by
    have := h.height_length
    simp only [height, List.take_of_length_le (le_refl w.length), sub_eq_zero] at this
    exact Nat.cast_injective this
  count_D_le_count_U i := (height_nonneg_iff w i).1 (h.height_nonneg i)

@[simp] theorem IsDyck.toDyckWord_toList {n : ℕ} (h : IsDyck n w) :
    h.toDyckWord.toList = w := rfl

theorem IsDyck.semilength_toDyckWord {n : ℕ} (h : IsDyck n w) :
    h.toDyckWord.semilength = n := by
  have hlen : 2 * h.toDyckWord.semilength = w.length :=
    DyckWord.two_mul_semilength_eq_length
  rw [h.length] at hlen; omega

/-- Conversely every `DyckWord` of semilength `n` satisfies `IsDyck n`. -/
theorem isDyck_of_dyckWord {n : ℕ} (p : DyckWord) (hp : p.semilength = n) :
    IsDyck n p.toList := by
  have hlen : p.toList.length = 2 * n := by
    rw [← hp]; exact DyckWord.two_mul_semilength_eq_length.symm
  refine ⟨hlen, ?_, fun i _ => (height_nonneg_iff _ i).2 (p.count_D_le_count_U i)⟩
  have := p.count_U_eq_count_D
  simp only [height, ← hlen, List.take_of_length_le (le_refl p.toList.length), sub_eq_zero]
  exact_mod_cast this

end Meanders
