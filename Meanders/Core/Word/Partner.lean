import Meanders.Core.Word

/-!
# Computing partners in a word

`Paired w l r` is the height rule for "`l` is matched to `r`". `partnerOf`
and `leftPartnerOf` compute the partner of a position by scanning heights,
in `O(length²)`, which is what an evaluator whose state is a word needs:
the first position after `l` at which the height comes back to its level
at `l` is the partner of an opener, and the last position before `r` at the
height after `r` is the partner of a closer. The specification lemmas
relating them to `Paired` are proved with the model that uses them.
-/

namespace Meanders

open DyckStep

instance instHashableDyckStepForMeanders : Hashable DyckStep :=
  ⟨fun s => match s with | U => 0 | D => 1⟩

/-- The partner of the opener at `l`: the first later position after which
the height is back to `height w l`. -/
def partnerOf (w : List DyckStep) (l : ℕ) : Option ℕ :=
  (List.range w.length).find? fun r => decide (l < r ∧ height w (r + 1) = height w l)

/-- The partner of the closer at `r`: the last earlier position at which the
height equals `height w (r + 1)`. -/
def leftPartnerOf (w : List DyckStep) (r : ℕ) : Option ℕ :=
  (List.range r).reverse.find? fun l => decide (height w l = height w (r + 1))

end Meanders

namespace Meanders

open DyckStep

variable {w : List DyckStep} {l r : ℕ}

/-- `range N` split at a position `r < N`. -/
theorem List.range_eq_append_cons {r N : ℕ} (h : r < N) :
    List.range N = List.range r ++ r :: (List.range (N - (r + 1))).map (r + 1 + ·) := by
  conv_lhs => rw [show N = (r + 1) + (N - (r + 1)) by omega, List.range_add, List.range_succ]
  simp

/-- `partnerOf` finds the partner of an opener. -/
theorem partnerOf_eq_of_paired (h : Paired w l r) : partnerOf w l = some r := by
  unfold partnerOf
  rw [List.find?_eq_some_iff_append]
  refine ⟨by simp [h.lt, h.height_eq], List.range r, _,
    List.range_eq_append_cons h.lt_length, ?_⟩
  intro r' hr'
  rw [List.mem_range] at hr'
  by_contra hcon
  simp at hcon
  have := h.height_lt (j := r' + 1) (by omega) (by omega)
  omega

/-- `leftPartnerOf` finds the partner of a closer. -/
theorem leftPartnerOf_eq_of_paired (h : Paired w l r) : leftPartnerOf w r = some l := by
  unfold leftPartnerOf
  rw [List.find?_eq_some_iff_append]
  refine ⟨by simp [h.height_eq], ((List.range (r - (l + 1))).map (l + 1 + ·)).reverse,
    (List.range l).reverse, ?_, ?_⟩
  · rw [List.range_eq_append_cons h.lt]
    simp
  · intro l' hl'
    simp only [List.mem_reverse, List.mem_map, List.mem_range] at hl'
    obtain ⟨k, hk, rfl⟩ := hl'
    by_contra hcon
    simp at hcon
    have h1 := h.height_lt (j := l + 1 + k) (by omega) (by omega)
    have h2 := h.height_eq
    omega

end Meanders
