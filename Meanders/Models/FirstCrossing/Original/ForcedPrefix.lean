import Meanders.Models.FirstCrossing.Original.Cut

/-!
# Forced old opening levels over every budget-feasible suffix

An old opening at level `j` lies below the current cut height `h`.
It remains unmatched throughout a continuation precisely when that
continuation stays strictly above level `j`. The suffix family below fixes
length and remaining down budget independently of this survival predicate.
-/

namespace Meanders.FirstCrossing

open DyckStep

/-- All ballot continuations with a prescribed length and remaining down budget. -/
structure BudgetSuffix (h len downs : ℕ) where
  /-- Original chronological continuation word. -/
  word : List DyckStep
  /-- Exactly the prescribed number of remaining steps. -/
  length_word : word.length = len
  /-- Exactly the remaining original down budget. -/
  count_down : word.count D = downs
  /-- The continuation never goes below the original baseline. -/
  prefix_nonneg : ∀ i, 0 ≤ (h : ℤ) + Dyck.height (word.take i)

/-- An old opening level survives if the continuation never descends to it. -/
def OldLevelSurvives {h len downs : ℕ} (s : BudgetSuffix h len downs) (j : ℕ) : Prop :=
  ∀ i, (j : ℤ) < (h : ℤ) + Dyck.height (s.word.take i)

/-- Spending all possible downs first reaches the smallest feasible height. -/
def lowestSuffix (h len downs : ℕ) : List DyckStep :=
  List.replicate (min h downs) D ++ List.replicate (len - downs) U ++
    List.replicate (downs - min h downs) D

private theorem lowestSuffix_length {h len downs : ℕ} (hd : downs ≤ len) :
    (lowestSuffix h len downs).length = len := by
  simp only [lowestSuffix, List.length_append, List.length_replicate]
  omega

private theorem lowestSuffix_count_down (h len downs : ℕ) :
    (lowestSuffix h len downs).count D = downs := by
  simp [lowestSuffix, List.count_replicate]

private theorem lowestSuffix_nonneg {h len downs : ℕ}
    (hfinal : downs ≤ h + (len - downs)) (i : ℕ) :
    0 ≤ (h : ℤ) + Dyck.height ((lowestSuffix h len downs).take i) := by
  simp only [lowestSuffix, List.take_append, List.length_append, List.length_replicate,
    List.take_replicate, Dyck.height_eq_count, List.count_append]
  simp [List.count_replicate]
  omega

/-- A genuine extremal continuation, rather than a survival predicate in disguise. -/
def lowestBudgetSuffix {h len downs : ℕ} (hd : downs ≤ len)
    (hfinal : downs ≤ h + (len - downs)) : BudgetSuffix h len downs where
  word := lowestSuffix h len downs
  length_word := lowestSuffix_length hd
  count_down := lowestSuffix_count_down h len downs
  prefix_nonneg := lowestSuffix_nonneg hfinal

/-- No continuation can spend more downs than its entire remaining down budget. -/
theorem BudgetSuffix.height_lower_bound {h len downs : ℕ} (s : BudgetSuffix h len downs)
    (i : ℕ) : ((h - downs : ℕ) : ℤ) ≤ (h : ℤ) + Dyck.height (s.word.take i) := by
  have hd : (s.word.take i).count D ≤ downs := by
    calc
      _ ≤ s.word.count D := (List.take_sublist i s.word).count_le D
      _ = downs := s.count_down
  have hn := s.prefix_nonneg i
  rw [Dyck.height_eq_count] at hn ⊢
  omega

/-- The explicit continuation attains the lower bound after its initial down run. -/
theorem lowestBudgetSuffix_attains {h len downs : ℕ} (hd : downs ≤ len)
    (hfinal : downs ≤ h + (len - downs)) :
    (h : ℤ) + Dyck.height
      ((lowestBudgetSuffix hd hfinal).word.take (min h downs)) = (h - downs : ℕ) := by
  simp [lowestBudgetSuffix, lowestSuffix, List.count_replicate, Dyck.height_eq_count]
  omega

/-- Exactly the bottom `h - downs` old levels survive every feasible suffix. -/
theorem forcedLevels_exact {h len downs j : ℕ} (hd : downs ≤ len)
    (hfinal : downs ≤ h + (len - downs)) :
    (∀ s : BudgetSuffix h len downs, OldLevelSurvives s j) ↔ j < h - downs := by
  constructor
  · intro hall
    have ha := hall (lowestBudgetSuffix hd hfinal) (min h downs)
    rw [lowestBudgetSuffix_attains hd hfinal] at ha
    exact_mod_cast ha
  · intro hj s i
    have := s.height_lower_bound i
    omega

/-- A ballot prefix translates height/remaining-budget slack into original counters. -/
theorem BallotHalf.forced_prefix_count {i h A : ℕ} (a : BallotHalf i h)
    (hc : a.word.count D ≤ A) : h - (A - a.word.count D) = i - A - a.word.count D := by
  have := a.length_eq_height_add_twice_down
  omega

/-- The exact old-level intersection in the original length/down-counter notation. -/
theorem BallotHalf.forcedLevels_exact {i h A len j : ℕ} (a : BallotHalf i h)
    (hc : a.word.count D ≤ A) (hd : A - a.word.count D ≤ len)
    (hfinal : A - a.word.count D ≤ h + (len - (A - a.word.count D))) :
    (∀ s : BudgetSuffix h len (A - a.word.count D), OldLevelSurvives s j) ↔
      j < i - A - a.word.count D := by
  rw [Meanders.FirstCrossing.forcedLevels_exact hd hfinal, a.forced_prefix_count hc]

/-- An opening stays unmatched exactly while later heights remain above its level. -/
theorem opening_unpaired_iff_above {w : List DyckStep} {l : ℕ}
    (hl : l < w.length) (hU : w[l]? = some U) :
    (¬ ∃ r, Paired w l r) ↔
      ∀ k, l < k → k ≤ w.length → height w l < height w k := by
  constructor
  · intro hn k hlk hkw
    by_contra hlow
    have hlen : l < (w.take k).length := by simp; omega
    have hstep : (w.take k)[l]? = some U := by
      simpa [List.getElem?_take, hlk] using hU
    have he : height (w.take k) (w.take k).length ≤ height (w.take k) l := by
      simp only [List.length_take, Nat.min_eq_left hkw, height, List.take_take,
        Nat.min_self, Nat.min_eq_left (by omega : l ≤ k)]
      simpa only [height] using (le_of_not_gt hlow)
    obtain ⟨r, hr⟩ := exists_paired_of_U hlen hstep he
    have hh : Paired (w.take k ++ w.drop k) l r :=
      (paired_append_left hr.lt_length).mpr hr
    rw [List.take_append_drop] at hh
    exact hn ⟨r, hh⟩
  · intro hh ⟨r, hr⟩
    have := hh (r + 1) (by have := hr.lt; omega) (by have := hr.lt_length; omega)
    rw [hr.height_eq] at this
    exact lt_irrefl _ this

/-- Older still-unmatched openings have strictly lower original height levels. -/
theorem oldOpening_level_lt {w : List DyckStep} {l k : ℕ}
    (hl : l < w.length) (hU : w[l]? = some U) (hold : ¬ ∃ r, Paired w l r)
    (hlk : l < k) (hk : k < w.length) : height w l < height w k :=
  (opening_unpaired_iff_above hl hU).mp hold k hlk hk.le

/-- Height-level survival is actual absence of a closing partner in the full word. -/
theorem oldLevelSurvives_iff_unpaired {i h len downs l j : ℕ} (a : BallotHalf i h)
    (s : BudgetSuffix h len downs) (hl : l < a.word.length) (hU : a.word[l]? = some U)
    (hold : ¬ ∃ r, Paired a.word l r) (hj : height a.word l = j) :
    OldLevelSurvives s j ↔ ¬ ∃ r, Paired (a.word ++ s.word) l r := by
  have hfull : l < (a.word ++ s.word).length := by simp; omega
  have hUfull : (a.word ++ s.word)[l]? = some U := by
    simpa [List.getElem?_append, hl] using hU
  rw [opening_unpaired_iff_above hfull hUfull]
  constructor
  · intro hs k hlk hkl
    rw [height_append_left (by omega : l ≤ a.word.length), hj]
    by_cases hk : k ≤ a.word.length
    · rw [height_append_left hk]
      rw [← hj]
      exact (opening_unpaired_iff_above hl hU).mp hold k hlk hk
    · have hsplit : k = a.word.length + (k - a.word.length) := by omega
      rw [hsplit, height_append_right]
      change (j : ℤ) < Dyck.height a.word + height s.word (k - a.word.length)
      rw [a.height_word, ← Dyck.height_take]
      exact hs _
  · intro hh k
    have hk : l < a.word.length + min k s.word.length := by omega
    have hlen : a.word.length + min k s.word.length ≤
        (a.word ++ s.word).length := by simp
    have ha := hh _ hk hlen
    rw [height_append_left (by omega : l ≤ a.word.length), hj,
      height_append_right] at ha
    change (j : ℤ) < Dyck.height a.word + height s.word (min k s.word.length) at ha
    rw [a.height_word] at ha
    have ht : s.word.take (min k s.word.length) = s.word.take k := by
      rw [← List.take_take, List.take_length]
    simpa only [Dyck.height_take, height, ht] using ha

/-- Forcedness quantified over physical source completions, expressed by old levels. -/
theorem BallotHalf.forcedOpening_exact {i h A len l j : ℕ} (a : BallotHalf i h)
    (hc : a.word.count D ≤ A) (hd : A - a.word.count D ≤ len)
    (hfinal : A - a.word.count D ≤ h + (len - (A - a.word.count D)))
    (hl : l < a.word.length) (hU : a.word[l]? = some U)
    (hold : ¬ ∃ r, Paired a.word l r) (hj : height a.word l = j) :
    (∀ s : BudgetSuffix h len (A - a.word.count D),
      ¬ ∃ r, Paired (a.word ++ s.word) l r) ↔ j < i - A - a.word.count D := by
  simpa only [oldLevelSurvives_iff_unpaired a _ hl hU hold hj] using
    a.forcedLevels_exact (j := j) hc hd hfinal

/-- Every level below the cut height is occupied by an old unmatched opening. -/
theorem BallotHalf.exists_oldOpening_level {i h j : ℕ} (a : BallotHalf i h) (hj : j < h) :
    ∃ l, l < a.word.length ∧ a.word[l]? = some U ∧
      (¬ ∃ r, Paired a.word l r) ∧ height a.word l = j := by
  let w := a.word ++ List.replicate h D
  let r := a.word.length + (h - 1 - j)
  have hr : r < w.length := by simp only [w, r, List.length_append, List.length_replicate]; omega
  have hrD : w[r]? = some D := by
    simp [w, r, List.getElem?_append, List.getElem?_replicate]
    omega
  have hrheight : height w (r + 1) = j := by
    have he : r + 1 = a.word.length + (h - j) := by dsimp [r]; omega
    rw [he]
    simp only [w, height_append_right]
    change Dyck.height a.word + height (List.replicate h D) (h - j) = j
    rw [a.height_word]
    simp [height, List.take_replicate, List.count_replicate]
    omega
  obtain ⟨l, hl⟩ := exists_paired_of_D hr hrD (by rw [hrheight]; omega)
  have hla : l < a.word.length := by
    by_contra hn
    have hu := hl.isU
    have hwl : l < w.length := hl.left_lt_length
    simp only [w, List.length_append, List.length_replicate] at hwl
    have hd : w[l]? = some D := by
      simp [w, List.getElem?_append, Nat.not_lt.mpr (Nat.le_of_not_gt hn),
        show l - a.word.length < h by omega]
    rw [hd] at hu
    contradiction
  have hU : a.word[l]? = some U := by
    have := hl.isU
    simpa [w, List.getElem?_append, hla] using this
  refine ⟨l, hla, hU, ?_, ?_⟩
  · rintro ⟨q, hq⟩
    have hqw : Paired w l q := (paired_append_left hq.lt_length).mpr hq
    have he := hl.right_unique hqw
    have hql := hq.lt_length
    dsimp [r] at he
    omega
  · have he := hl.height_eq
    rw [hrheight] at he
    change (j : ℤ) = height (a.word ++ List.replicate h D) l at he
    rw [height_append_left hla.le] at he
    exact he.symm

/-- Physical positions of the old unmatched openings, ordered chronologically. -/
noncomputable def oldOpenings (w : List DyckStep) : Finset ℕ := by
  classical
  exact (Finset.range w.length).filter fun l => w[l]? = some U ∧ ¬ ∃ r, Paired w l r

@[simp] theorem mem_oldOpenings {w : List DyckStep} {l : ℕ} :
    l ∈ oldOpenings w ↔ l < w.length ∧ w[l]? = some U ∧ ¬ ∃ r, Paired w l r := by
  classical
  simp [oldOpenings]

/-- Height order and chronological order agree on the old opening set. -/
theorem oldOpenings_level_order {w : List DyckStep} {l k : ℕ}
    (hl : l ∈ oldOpenings w) (hk : k ∈ oldOpenings w) :
    height w l < height w k ↔ l < k := by
  obtain ⟨hll, hlU, hln⟩ := mem_oldOpenings.mp hl
  obtain ⟨hkl, hkU, hkn⟩ := mem_oldOpenings.mp hk
  constructor
  · intro hh
    rcases lt_trichotomy l k with he | he | he
    · exact he
    · subst k; omega
    · have := oldOpening_level_lt hkl hkU hkn he hll
      omega
  · intro hh
    exact oldOpening_level_lt hll hlU hln hh hkl

private theorem BallotHalf.oldOpenings_level_injective {i h : ℕ} (a : BallotHalf i h) :
    Set.InjOn (fun l => (height a.word l).toNat) (oldOpenings a.word : Set ℕ) := by
  intro l hl k hk he
  dsimp only at he
  have hn := a.prefix_nonneg l
  have hn' := a.prefix_nonneg k
  rw [Dyck.height_take] at hn hn'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := (oldOpenings_level_order hl hk).mpr hlt
    omega
  · have := (oldOpenings_level_order hk hl).mpr hgt
    omega

/-- Exactly `J` old openings lie below level `J`, for every `J ≤ h`. -/
theorem BallotHalf.oldOpenings_below_card {i h J : ℕ} (a : BallotHalf i h) (hJ : J ≤ h) :
    ((oldOpenings a.word).filter fun l => (height a.word l).toNat < J).card = J := by
  classical
  conv_rhs => rw [← Finset.card_range J]
  refine Finset.card_bij (fun l _ => (height a.word l).toNat) ?_ ?_ ?_
  · intro l hl
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hl).2
  · intro l hl k hk he
    exact a.oldOpenings_level_injective (Finset.mem_filter.mp hl).1
      (Finset.mem_filter.mp hk).1 he
  · intro j hj
    have hjJ := Finset.mem_range.mp hj
    obtain ⟨l, hll, hlU, hln, hlevel⟩ := a.exists_oldOpening_level (j := j) (by omega)
    refine ⟨l, Finset.mem_filter.mpr ⟨mem_oldOpenings.mpr ⟨hll, hlU, hln⟩, ?_⟩, ?_⟩
    · simpa only [hlevel, Int.toNat_natCast] using hjJ
    · simp only [hlevel, Int.toNat_natCast]

/-- An old opening's original height is its oldest-first ordinal. -/
theorem BallotHalf.oldOpening_ordinal {i h l : ℕ} (a : BallotHalf i h)
    (hl : l ∈ oldOpenings a.word) :
    ((oldOpenings a.word).filter (· < l)).card = (height a.word l).toNat := by
  classical
  have hn := a.prefix_nonneg l
  rw [Dyck.height_take] at hn
  have hm := mem_oldOpenings.mp hl
  have hh := (opening_unpaired_iff_above hm.1 hm.2.1).mp hm.2.2
    a.word.length hm.1 le_rfl
  change height a.word l < Dyck.height a.word at hh
  rw [a.height_word] at hh
  have he : (oldOpenings a.word).filter (· < l) =
      (oldOpenings a.word).filter (fun k => (height a.word k).toNat <
        (height a.word l).toNat) := by
    apply Finset.filter_congr
    intro k hk
    have hkn := a.prefix_nonneg k
    rw [Dyck.height_take] at hkn
    have ho := oldOpenings_level_order hk hl
    omega
  rw [he]
  exact a.oldOpenings_below_card (by omega)

/-- The oldest `count` old openings, selected by physical chronological ordinal. -/
noncomputable def oldestOpenings (w : List DyckStep) (count : ℕ) : Finset ℕ := by
  classical
  exact (oldOpenings w).filter fun l => ((oldOpenings w).filter (· < l)).card < count

/-- Intersection of actual old openings left unmatched in every feasible completion. -/
noncomputable def forcedOpenings {i h : ℕ} (a : BallotHalf i h) (A len : ℕ) : Finset ℕ := by
  classical
  exact (oldOpenings a.word).filter fun l =>
    ∀ s : BudgetSuffix h len (A - a.word.count D), ¬ ∃ r, Paired (a.word ++ s.word) l r

/-- Exact forced-prefix contract: the physical intersection is the oldest `i-A-c` openings. -/
theorem forcedPrefix_exact {i h A len : ℕ} (a : BallotHalf i h)
    (hc : a.word.count D ≤ A) (hd : A - a.word.count D ≤ len)
    (hfinal : A - a.word.count D ≤ h + (len - (A - a.word.count D))) :
    forcedOpenings a A len = oldestOpenings a.word (i - A - a.word.count D) := by
  classical
  apply Finset.filter_congr
  intro l hl
  obtain ⟨hll, hlU, hln⟩ := mem_oldOpenings.mp hl
  have hn := a.prefix_nonneg l
  rw [Dyck.height_take] at hn
  have hlevel : height a.word l = ((height a.word l).toNat : ℤ) :=
    (Int.toNat_of_nonneg hn).symm
  rw [a.oldOpening_ordinal hl]
  exact a.forcedOpening_exact hc hd hfinal hll hlU hln hlevel

/-- Below the cut height, the oldest-prefix selector has its stated cardinality. -/
theorem BallotHalf.oldestOpenings_card {i h count : ℕ} (a : BallotHalf i h)
    (hc : count ≤ h) : (oldestOpenings a.word count).card = count := by
  classical
  have he : oldestOpenings a.word count =
      (oldOpenings a.word).filter (fun l => (height a.word l).toNat < count) := by
    apply Finset.filter_congr
    intro l hl
    rw [a.oldOpening_ordinal hl]
  rw [he]
  exact a.oldOpenings_below_card hc

/-- The number of forced physical openings is the original-counter slack. -/
theorem forcedOpenings_card {i h A len : ℕ} (a : BallotHalf i h)
    (hc : a.word.count D ≤ A) (hd : A - a.word.count D ≤ len)
    (hfinal : A - a.word.count D ≤ h + (len - (A - a.word.count D))) :
    (forcedOpenings a A len).card = i - A - a.word.count D := by
  rw [forcedPrefix_exact a hc hd hfinal]
  apply a.oldestOpenings_card
  have := a.forced_prefix_count hc
  omega

end Meanders.FirstCrossing
