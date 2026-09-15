import Meanders.Core.Matching.Prefix
import Meanders.Core.Word.Intrinsic.Reflection

/-!
# Independent inward ballot halves

A cut reads the left part of a matching word forwards and the right part
backwards with open/close exchanged. Both parts are ordinary nonnegative
ballot paths ending at the cut height. Conversely, *any* two such paths
reconstruct a matching. No image predicate hides a compatibility condition.
-/

namespace Meanders.FirstCrossing

open DyckStep

/-- An independently specified inward ballot path of length `len`, ending at `h`. -/
structure BallotHalf (len h : Nat) where
  /-- Original inward steps, including openings later removed by forced joins. -/
  word : List DyckStep
  length_word : word.length = len
  height_word : Dyck.height word = h
  prefix_nonneg : ∀ i, 0 ≤ Dyck.height (word.take i)

@[ext] theorem BallotHalf.ext {len h : Nat} {a b : BallotHalf len h}
    (hw : a.word = b.word) : a = b := by
  cases a
  cases b
  cases hw
  rfl

theorem BallotHalf.length_eq_height_add_twice_down {len h : Nat}
    (a : BallotHalf len h) : len = h + 2 * a.word.count D := by
  have hc := count_U_add_count_D a.word
  have hh := a.height_word
  rw [Dyck.height_eq_count] at hh
  have hl := a.length_word
  omega

/-- The original down budget is determined by the original half length and height. -/
theorem BallotHalf.down_budget {len h : Nat} (a : BallotHalf len h) :
    a.word.count D = (len - h) / 2 := by
  have := a.length_eq_height_add_twice_down
  omega

theorem BallotHalf.height_le_length {len h : Nat} (a : BallotHalf len h) : h ≤ len := by
  have := a.length_eq_height_add_twice_down
  omega

private theorem height_reflected_prefix (word : List DyckStep) (i : Nat) :
    Dyck.height ((Dyck.reverseComplement word).take i) =
      Dyck.height (word.take (word.length - i)) - Dyck.height word := by
  rw [Dyck.take_reverseComplement, Dyck.height_reverseComplement]
  have hs : Dyck.height (word.take (word.length - i)) +
      Dyck.height (word.drop (word.length - i)) = Dyck.height word := by
    rw [← Dyck.height_append, List.take_append_drop]
  omega

/-- Reconstruct the physical left-to-right word from the two inward words. -/
def joinHalves {l r h : Nat} (a : BallotHalf l h) (b : BallotHalf r h) :
    List DyckStep := a.word ++ Dyck.reverseComplement b.word

@[simp] theorem length_joinHalves {l r h : Nat}
    (a : BallotHalf l h) (b : BallotHalf r h) :
    (joinHalves a b).length = l + r := by
  simp [joinHalves, a.length_word, b.length_word]

theorem joinHalves_balanced {l r h : Nat} (a : BallotHalf l h) (b : BallotHalf r h) :
    Balanced (joinHalves a b) := by
  rw [balanced_iff_height]
  constructor
  · change Dyck.height (joinHalves a b) = 0
    simp [joinHalves, a.height_word, b.height_word]
  · intro i
    rw [← Dyck.height_take]
    by_cases hi : i ≤ a.word.length
    · simpa [joinHalves, List.take_append_of_le_length hi] using a.prefix_nonneg i
    · rw [joinHalves, List.take_append, List.take_of_length_le (by omega),
        Dyck.height_append, height_reflected_prefix, a.height_word, b.height_word]
      have := b.prefix_nonneg (b.word.length - (i - a.word.length))
      omega

@[simp] theorem take_joinHalves {l r h : Nat}
    (a : BallotHalf l h) (b : BallotHalf r h) :
    (joinHalves a b).take l = a.word := by
  simp [joinHalves, ← a.length_word]

@[simp] theorem drop_joinHalves {l r h : Nat}
    (a : BallotHalf l h) (b : BallotHalf r h) :
    (joinHalves a b).drop l = Dyck.reverseComplement b.word := by
  simp [joinHalves, ← a.length_word]

/-- Matchings whose height at the physical cut is the prescribed height. -/
def MatchingAtCut (n cut h : Nat) :=
  {m : NoncrossingMatching n // Meanders.height m.wordOf cut = h}

/-- Extract the left inward half. -/
def leftHalf {n cut h : Nat} (hc : cut ≤ 2 * n) (m : MatchingAtCut n cut h) :
    BallotHalf cut h where
  word := m.val.wordOf.take cut
  length_word := by simp [List.length_take, m.val.length_wordOf, Nat.min_eq_left hc]
  height_word := by rw [Dyck.height_take]; exact m.property
  prefix_nonneg i := by
    rw [List.take_take, Dyck.height_take]
    exact m.val.isDyck_wordOf.height_nonneg _

/-- Extract the right inward half by physical reverse-complement. -/
def rightHalf {n cut h : Nat} (hc : cut ≤ 2 * n) (m : MatchingAtCut n cut h) :
    BallotHalf (2 * n - cut) h where
  word := Dyck.reverseComplement (m.val.wordOf.drop cut)
  length_word := by simp [m.val.length_wordOf]
  height_word := by
    rw [Dyck.height_reverseComplement]
    have hs : Dyck.height (m.val.wordOf.take cut) +
        Dyck.height (m.val.wordOf.drop cut) = 0 := by
      rw [← Dyck.height_append, List.take_append_drop]
      exact m.val.isDyck_wordOf.height_length
    rw [Dyck.height_take, m.property] at hs
    omega
  prefix_nonneg i := by
    have hb := (Balanced.of_isDyck m.val.isDyck_wordOf).reverseComplement
    have he : Dyck.reverseComplement (m.val.wordOf.drop cut) =
        (Dyck.reverseComplement m.val.wordOf).take (2 * n - cut) := by
      rw [Dyck.take_reverseComplement, m.val.length_wordOf,
        Nat.sub_sub_self hc]
    rw [he, List.take_take]
    exact hb.height_nonneg_take _

/-- Reconstruct using the existing balanced-word-to-matching construction. -/
def matchingOfHalves {n cut h : Nat} (hc : cut ≤ 2 * n)
    (a : BallotHalf cut h) (b : BallotHalf (2 * n - cut) h) : MatchingAtCut n cut h := by
  have hw : IsDyck n (joinHalves a b) := by
    have hl : (joinHalves a b).length = 2 * n := by simp; omega
    have hb := joinHalves_balanced a b
    refine ⟨hl, ?_, fun i _ => hb.height_nonneg i⟩
    simpa only [hl] using hb.height_length
  refine ⟨ofDyck hw, ?_⟩
  rw [wordOf_ofDyck, ← Dyck.height_take, take_joinHalves]
  exact a.height_word

@[simp] theorem wordOf_matchingOfHalves {n cut h : Nat} (hc : cut ≤ 2 * n)
    (a : BallotHalf cut h) (b : BallotHalf (2 * n - cut) h) :
    (matchingOfHalves hc a b).val.wordOf = joinHalves a b := by
  dsimp only [matchingOfHalves]
  exact wordOf_ofDyck _

/-- The right endpoints of through arches occur in reverse physical order.
Thus both inward scans encounter through partners in the same oldest-first order. -/
theorem through_partner_reverse_order {n cut : Nat} (m : NoncrossingMatching n)
    {a b : Point n} (ha : a ∈ m.active cut) (hb : b ∈ m.active cut) :
    a < b ↔ m.partner b < m.partner a := by
  have ha' := m.mem_active.mp ha
  have hb' := m.mem_active.mp hb
  constructor
  · intro hab
    by_contra hp
    have hne : m.partner a ≠ m.partner b := by
      intro he
      have := congrArg m.partner he
      simp only [m.partner_partner] at this
      exact (ne_of_lt hab) this
    have hp' : m.partner a < m.partner b := lt_of_le_of_ne (le_of_not_gt hp) hne
    exact m.not_interleave rfl rfl hab
      (show b.val < (m.partner a).val from lt_of_lt_of_le hb'.1 ha'.2) hp'
  · intro hp
    by_contra hab
    have hne : b ≠ a := by
      intro he
      subst b
      exact (lt_irrefl _ hp)
    have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab) hne
    exact m.not_interleave rfl rfl hba
      (show a.val < (m.partner b).val from lt_of_lt_of_le ha'.1 hb'.2) hp

/-- Original left ordinal equals original right inward ordinal. Ordinals count
older through endpoints, so the oldest pair has ordinal zero on both sides. -/
theorem through_pair_ordinal {n cut : Nat} (m : NoncrossingMatching n)
    {a : Point n} (ha : a ∈ m.active cut) :
    ((m.active cut).filter (· < a)).card =
      (((m.active cut).image m.partner).filter (m.partner a < ·)).card := by
  have he : ((m.active cut).filter (· < a)).image m.partner =
      ((m.active cut).image m.partner).filter (m.partner a < ·) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨b, ⟨hb, hba⟩, rfl⟩
      exact ⟨⟨b, hb, rfl⟩, (through_partner_reverse_order m hb ha).mp hba⟩
    · rintro ⟨⟨b, hb, rfl⟩, hp⟩
      exact ⟨b, ⟨hb, (through_partner_reverse_order m hb ha).mpr hp⟩, rfl⟩
  rw [← he, Finset.card_image_of_injective]
  intro a b heq
  have := congrArg m.partner heq
  simpa only [m.partner_partner] using this

/-- Cutting and reconstruction are an actual equivalence of independent ballot paths. -/
def asymmetricCutEquiv (n cut h : Nat) (hc : cut ≤ 2 * n) :
    MatchingAtCut n cut h ≃ BallotHalf cut h × BallotHalf (2 * n - cut) h where
  toFun m := (leftHalf hc m, rightHalf hc m)
  invFun p := matchingOfHalves hc p.1 p.2
  left_inv m := by
    apply Subtype.ext
    apply NoncrossingMatching.ext
    rw [← (matchingOfHalves hc (leftHalf hc m) (rightHalf hc m)).val.archesOfWord_wordOf,
      wordOf_matchingOfHalves]
    simp only [joinHalves, leftHalf, rightHalf, Dyck.reverseComplement_reverseComplement,
      List.take_append_drop]
    exact m.val.archesOfWord_wordOf
  right_inv p := by
    apply Prod.ext
    · apply BallotHalf.ext
      change (matchingOfHalves hc p.1 p.2).val.wordOf.take cut = p.1.word
      simp
    · apply BallotHalf.ext
      change Dyck.reverseComplement ((matchingOfHalves hc p.1 p.2).val.wordOf.drop cut) =
        p.2.word
      simp

@[simp] theorem leftHalf_word {n cut h : Nat} (hc : cut ≤ 2 * n)
    (m : MatchingAtCut n cut h) : (leftHalf hc m).word = m.val.wordOf.take cut := rfl

@[simp] theorem rightHalf_word {n cut h : Nat} (hc : cut ≤ 2 * n)
    (m : MatchingAtCut n cut h) :
    (rightHalf hc m).word = Dyck.reverseComplement (m.val.wordOf.drop cut) := rfl

@[simp] theorem leftHalf_matchingOfHalves {n cut h : Nat} (hc : cut ≤ 2 * n)
    (a : BallotHalf cut h) (b : BallotHalf (2 * n - cut) h) :
    leftHalf hc (matchingOfHalves hc a b) = a := by
  apply BallotHalf.ext
  simp

@[simp] theorem rightHalf_matchingOfHalves {n cut h : Nat} (hc : cut ≤ 2 * n)
    (a : BallotHalf cut h) (b : BallotHalf (2 * n - cut) h) :
    rightHalf hc (matchingOfHalves hc a b) = b := by
  apply BallotHalf.ext
  simp

@[simp] theorem matchingOfHalves_extract {n cut h : Nat} (hc : cut ≤ 2 * n)
    (m : MatchingAtCut n cut h) :
    matchingOfHalves hc (leftHalf hc m) (rightHalf hc m) = m :=
  (asymmetricCutEquiv n cut h hc).left_inv m

end Meanders.FirstCrossing
