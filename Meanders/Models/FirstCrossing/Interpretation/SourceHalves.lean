import Meanders.Models.FirstCrossing.Original.Cut
import Meanders.Models.FirstCrossing.Native.State

/-!
# Independent source words in each first-crossing sector

The HIGH source uses four independent ballot halves and tests the original
left prefixes directly. Reconstruction through the established cut equivalence
identifies it with the matching-pair source sector. No frontier state or
executable transition is part of this source-language equivalence.
-/

namespace Meanders.FirstCrossing

/-- The original left first-hit test, applied directly to the two ballot words. -/
def LeftFirstHit (K L : Nat) (pl ql : List DyckStep) : Prop :=
  (L : Int) - downs pl L - downs ql L = K ∧
    ∀ i, i < L → (i : Int) - downs pl i - downs ql i < K

/-- Four independent inward ballot words with the oriented HIGH metadata and
the original chronological left first-hit test. -/
structure HighSource (n K L u v : Nat) where
  /-- The original physical cut lies inside the full boundary. -/
  cut_le : L ≤ 2 * n
  /-- Upper original left inward word. -/
  pl : BallotHalf L u
  /-- Upper reflected-right inward word. -/
  pr : BallotHalf (2 * n - L) u
  /-- Lower original left inward word. -/
  ql : BallotHalf L v
  /-- Lower reflected-right inward word. -/
  qr : BallotHalf (2 * n - L) v
  /-- The direct original-left counter filter. -/
  first_hit : LeftFirstHit K L pl.word ql.word

@[ext] theorem HighSource.ext {n K L u v : Nat} {a b : HighSource n K L u v}
    (hpl : a.pl = b.pl) (hpr : a.pr = b.pr) (hql : a.ql = b.ql) (hqr : a.qr = b.qr) :
    a = b := by
  cases a
  cases b
  cases hpl
  cases hpr
  cases hql
  cases hqr
  rfl

/-- Reconstructing right halves does not affect any original left down counter. -/
theorem downs_matchingOfHalves_left {n L h i : Nat} (hL : L ≤ 2 * n)
    (a : BallotHalf L h) (b : BallotHalf (2 * n - L) h) (hi : i ≤ L) :
    downs (matchingOfHalves hL a b).val.wordOf i = downs a.word i := by
  rw [wordOf_matchingOfHalves]
  simp only [downs, joinHalves,
    List.take_append_of_le_length (show i ≤ a.word.length by simpa [a.length_word] using hi)]

/-- HIGH reconstruction uses the existing inverse cut maps for both owners. -/
def HighSource.matchings {n K L u v : Nat} (s : HighSource n K L u v) :
    NoncrossingMatching n × NoncrossingMatching n :=
  (((asymmetricCutEquiv n L u s.cut_le).symm (s.pl, s.pr)).val,
    ((asymmetricCutEquiv n L v s.cut_le).symm (s.ql, s.qr)).val)

@[simp] theorem HighSource.wordOf_upper {n K L u v : Nat} (s : HighSource n K L u v) :
    s.matchings.1.wordOf = joinHalves s.pl s.pr :=
  wordOf_matchingOfHalves s.cut_le s.pl s.pr

@[simp] theorem HighSource.wordOf_lower {n K L u v : Nat} (s : HighSource n K L u v) :
    s.matchings.2.wordOf = joinHalves s.ql s.qr :=
  wordOf_matchingOfHalves s.cut_le s.ql s.qr

/-- The right source words are precisely the physical right suffixes read inward. -/
theorem HighSource.right_suffixes {n K L u v : Nat} (s : HighSource n K L u v) :
    Dyck.reverseComplement (s.matchings.1.wordOf.drop L) = s.pr.word ∧
      Dyck.reverseComplement (s.matchings.2.wordOf.drop L) = s.qr.word := by
  simp

theorem HighSource.grade_left {n K L u v : Nat} (s : HighSource n K L u v)
    {i : Nat} (hi : i ≤ L) :
    grade s.matchings.1 s.matchings.2 i =
      (i : Int) - downs s.pl.word i - downs s.ql.word i := by
  change (i : Int) - downs (matchingOfHalves s.cut_le s.pl s.pr).val.wordOf i -
    downs (matchingOfHalves s.cut_le s.ql s.qr).val.wordOf i = _
  rw [downs_matchingOfHalves_left _ _ _ hi, downs_matchingOfHalves_left _ _ _ hi]

theorem HighSource.inSector {n K L u v : Nat} (s : HighSource n K L u v) :
    InSector K s.matchings.1 s.matchings.2 (.high L u v) := by
  refine ⟨⟨s.cut_le, ?_, ?_⟩, ?_, ?_⟩
  · rw [s.grade_left le_rfl]
    exact s.first_hit.1
  · intro i hi
    rw [s.grade_left hi.le]
    exact s.first_hit.2 i hi
  · exact (matchingOfHalves s.cut_le s.pl s.pr).property
  · exact (matchingOfHalves s.cut_le s.ql s.qr).property

/-- Extract both pairs of inward words and retain the source's direct first-hit
test, with no predicate on reconstructed matchings in the resulting type. -/
def highSourceOfMatchings {n K L u v : Nat}
    (p : {p : NoncrossingMatching n × NoncrossingMatching n //
      InSector K p.1 p.2 (.high L u v)}) : HighSource n K L u v where
  cut_le := p.property.1.1
  pl := leftHalf p.property.1.1 ⟨p.val.1, p.property.2.1⟩
  pr := rightHalf p.property.1.1 ⟨p.val.1, p.property.2.1⟩
  ql := leftHalf p.property.1.1 ⟨p.val.2, p.property.2.2⟩
  qr := rightHalf p.property.1.1 ⟨p.val.2, p.property.2.2⟩
  first_hit := by
    constructor
    · simpa only [leftHalf, grade, downs, List.take_take, Nat.min_self]
        using p.property.1.2.1
    · intro i hi
      simpa only [leftHalf, grade, downs, List.take_take, Nat.min_eq_left hi.le]
        using p.property.1.2.2 i hi

/-- Exact HIGH source-language equivalence, including its independently defined
original left first-hit filter. -/
def highSourceEquiv (n K L u v : Nat) : HighSource n K L u v ≃
    {p : NoncrossingMatching n × NoncrossingMatching n //
      InSector K p.1 p.2 (.high L u v)} where
  toFun s := ⟨s.matchings, s.inSector⟩
  invFun := highSourceOfMatchings
  left_inv s := by
    apply HighSource.ext
    · change leftHalf s.cut_le (matchingOfHalves s.cut_le s.pl s.pr) = s.pl
      simp
    · change rightHalf s.cut_le (matchingOfHalves s.cut_le s.pl s.pr) = s.pr
      simp
    · change leftHalf s.cut_le (matchingOfHalves s.cut_le s.ql s.qr) = s.ql
      simp
    · change rightHalf s.cut_le (matchingOfHalves s.cut_le s.ql s.qr) = s.qr
      simp
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (matchingOfHalves_extract p.property.1.1
        (⟨p.val.1, p.property.2.1⟩ : MatchingAtCut n L u))
    · exact congrArg Subtype.val (matchingOfHalves_extract p.property.1.1
        (⟨p.val.2, p.property.2.2⟩ : MatchingAtCut n L v))

/-- Full inward ballot words ending at height zero are precisely matching words. -/
def fullBallotEquiv (n : Nat) : BallotHalf (2 * n) 0 ≃ NoncrossingMatching n where
  toFun a := ofDyck ⟨a.length_word, by
    simpa only [Dyck.height, a.length_word, Nat.cast_zero] using a.height_word,
    fun i _ => by rw [← Dyck.height_take]; exact a.prefix_nonneg i⟩
  invFun m := {
    word := m.wordOf
    length_word := m.length_wordOf
    height_word := m.isDyck_wordOf.height_length
    prefix_nonneg := fun i => by rw [Dyck.height_take]; exact m.isDyck_wordOf.height_nonneg i }
  left_inv a := by
    apply BallotHalf.ext
    exact wordOf_ofDyck _
  right_inv m := by
    apply NoncrossingMatching.ext
    exact m.archesOfWord_wordOf

@[simp] theorem wordOf_fullBallotEquiv {n : Nat} (a : BallotHalf (2 * n) 0) :
    (fullBallotEquiv n a).wordOf = a.word := by
  dsimp only [fullBallotEquiv, Equiv.coe_fn_mk]
  exact wordOf_ofDyck _

@[simp] theorem word_fullBallotEquiv_symm {n : Nat} (m : NoncrossingMatching n) :
    ((fullBallotEquiv n).symm m).word = m.wordOf := rfl

/-- The LOW source is two independent full ballot words, with the original
chronological grade below the threshold at every prefix. -/
structure LowSource (n K : Nat) where
  /-- Complete upper ballot word. -/
  upper : BallotHalf (2 * n) 0
  /-- Complete lower ballot word. -/
  lower : BallotHalf (2 * n) 0
  /-- The direct original-counter LOW filter at every prefix. -/
  below : ∀ i, i ≤ 2 * n →
    (i : Int) - downs upper.word i - downs lower.word i < K

@[ext] theorem LowSource.ext {n K : Nat} {a b : LowSource n K}
    (hu : a.upper = b.upper) (hl : a.lower = b.lower) : a = b := by
  cases a
  cases b
  cases hu
  cases hl
  rfl

/-- Exact LOW source-language equivalence; the filter is stated on the original
full words before any matching reconstruction. -/
def lowSourceEquiv (n K : Nat) : LowSource n K ≃
    {p : NoncrossingMatching n × NoncrossingMatching n // InSector K p.1 p.2 .low} where
  toFun s := ⟨(fullBallotEquiv n s.upper, fullBallotEquiv n s.lower), by
    intro i hi
    simpa only [grade, wordOf_fullBallotEquiv] using s.below i hi⟩
  invFun p := {
    upper := (fullBallotEquiv n).symm p.val.1
    lower := (fullBallotEquiv n).symm p.val.2
    below := p.property }
  left_inv s := by
    apply LowSource.ext
    · exact (fullBallotEquiv n).symm_apply_apply s.upper
    · exact (fullBallotEquiv n).symm_apply_apply s.lower
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (fullBallotEquiv n).apply_symm_apply p.val.1
    · exact (fullBallotEquiv n).apply_symm_apply p.val.2

/-- One source language over the actual native sector. Both alternatives retain
their independently stated original-word prefix filters. -/
def Source (spec : RunSpec) : Type :=
  match spec.sector with
  | .low => LowSource spec.n spec.K
  | .high L u v => HighSource spec.n spec.K L u v

/-- Reconstructed ordered physical source pair, for either sector. -/
def Source.matchings {spec : RunSpec} (s : Source spec) :
    NoncrossingMatching spec.n × NoncrossingMatching spec.n :=
  match spec with
  | ⟨n, K, .low⟩ => (lowSourceEquiv n K s).val
  | ⟨_, _, .high _ _ _⟩ => HighSource.matchings s

/-- The shared source language is exactly the specified matching-pair sector. -/
def sourceEquiv (spec : RunSpec) : Source spec ≃
    {p : NoncrossingMatching spec.n × NoncrossingMatching spec.n //
      InSector spec.K p.1 p.2 spec.sector} :=
  match spec with
  | ⟨n, K, .low⟩ => lowSourceEquiv n K
  | ⟨n, K, .high L u v⟩ => highSourceEquiv n K L u v

theorem Source.inSector {spec : RunSpec} (s : Source spec) :
    InSector spec.K s.matchings.1 s.matchings.2 spec.sector := by
  cases spec with
  | mk n K sector =>
    cases sector with
    | low => exact (lowSourceEquiv n K s).property
    | high L u v => exact HighSource.inSector s

end Meanders.FirstCrossing
