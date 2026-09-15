import Meanders.Models.FirstCrossing.Original.Cut
import Meanders.Core.Matching.Exterior
import Meanders.Core.Matching.Reflection

/-!
# Original exterior events at an inward cut

An exterior arch is either wholly left, wholly right, or crosses the cut.
The first two classes are detected by down steps from height one in the
actual inward ballot words. Positive cut height gives exactly one exterior
through arch. The marking equivalence is established before cardinalities;
no event predicate mentions exteriority or an executable frontier state.
-/

namespace Meanders.FirstCrossing

open DyckStep

/-- An event is an actual original down step starting at height one. -/
def ReturnEvent (w : List DyckStep) :=
  {i : Fin w.length // w[i.val]? = some D ∧ Meanders.height w i.val = 1}

instance (w : List DyckStep) : Fintype (ReturnEvent w) :=
  inferInstanceAs (Fintype {_i : Fin w.length // _})

/-- Exteriority is read at the original opener, before any frontier contraction. -/
theorem exterior_iff_opener_height_zero {n : Nat} (m : NoncrossingMatching n)
    {a : Arch n} (ha : a ∈ m.arches) :
    a ∈ m.exteriorArches ↔ Meanders.height m.wordOf a.left.val = 0 := by
  rw [m.mem_exteriorArches_iff_active_empty ha, ← m.card_active (by omega)]
  simp

/-- Exterior arches close at original height one. -/
theorem exterior_iff_closer_height_one {n : Nat} (m : NoncrossingMatching n)
    {a : Arch n} (ha : a ∈ m.arches) :
    a ∈ m.exteriorArches ↔ Meanders.height m.wordOf a.right.val = 1 := by
  have hp := m.paired_wordOf ha
  have hh := hp.height_eq
  have hd := height_succ_of_D hp.isD
  rw [exterior_iff_opener_height_zero m ha]
  omega

private theorem height_take (w : List DyckStep) {i k : Nat} (hi : i ≤ k) :
    Meanders.height (w.take k) i = Meanders.height w i := by
  simp [Meanders.height, List.take_take, Nat.min_eq_left hi]

/-- Prefix return events are literally the whole-word events before the cut. -/
theorem returnEvent_take_iff {w : List DyckStep} {i k : Nat} (hi : i < k) :
    (w.take k)[i]? = some D ∧ Meanders.height (w.take k) i = 1 ↔
      w[i]? = some D ∧ Meanders.height w i = 1 := by
  rw [List.getElem?_take, ite_eq_left hi, height_take w hi.le]

/-- The height in the physical reflected prefix is the original height at
its complementary cut. This uses the original word, never retained ports. -/
theorem height_reverse_prefix {w : List DyckStep} (hw : Balanced w) (i : Nat) :
    Meanders.height (Dyck.reverseComplement w) i = Meanders.height w (w.length - i) := by
  rw [← Dyck.height_take, Dyck.take_reverseComplement, Dyck.height_reverseComplement]
  have hh : Dyck.height (w.take (w.length - i)) +
      Dyck.height (w.drop (w.length - i)) = 0 := by
    rw [← Dyck.height_append, List.take_append_drop]
    exact hw.height_length
  rw [Dyck.height_take] at hh
  omega

/-- The incident arch of a down step has that step as its right endpoint. -/
theorem archAt_right_of_D {n : Nat} (m : NoncrossingMatching n) (v : Point n)
    (hv : m.wordOf[v.val]? = some D) : (m.archAt v).right = v := by
  rcases m.archAt_contains v with hopen | hclose
  · have hp := (m.paired_wordOf (m.archAt_mem v)).isU
    rw [← hopen] at hp
    rw [hv] at hp
    contradiction
  · exact hclose.symm

/-- The incident arch of an up step has that step as its left endpoint. -/
theorem archAt_left_of_U {n : Nat} (m : NoncrossingMatching n) (v : Point n)
    (hv : m.wordOf[v.val]? = some U) : (m.archAt v).left = v := by
  rcases m.archAt_contains v with hopen | hclose
  · exact hopen.symm
  · have hp := (m.paired_wordOf (m.archAt_mem v)).isD
    rw [← hclose] at hp
    rw [hv] at hp
    contradiction

/-- Two distinct exterior arches have disjoint physical intervals. -/
theorem exterior_separated {n : Nat} (m : NoncrossingMatching n)
    {a b : Arch n} (ha : a ∈ m.exteriorArches) (hb : b ∈ m.exteriorArches)
    (hne : a ≠ b) : a.right < b.left ∨ b.right < a.left := by
  have ham := (m.mem_exteriorArches.mp ha).1
  have hbm := (m.mem_exteriorArches.mp hb).1
  rcases Arch.separated_or_nested (m.disjointEndpoints ham hbm hne)
      (m.not_crosses ham hbm) with hs | hs | he | he
  · exact Or.inl hs
  · exact Or.inr hs
  · exact ((m.mem_exteriorArches.mp hb).2 a ham he).elim
  · exact ((m.mem_exteriorArches.mp ha).2 b hbm he).elim

/-- At most one exterior arch crosses a physical cut. -/
theorem exterior_through_unique {n cut : Nat} (m : NoncrossingMatching n)
    {a b : Arch n} (ha : a ∈ m.exteriorArches) (hb : b ∈ m.exteriorArches)
    (hac : a.left.val < cut ∧ cut ≤ a.right.val)
    (hbc : b.left.val < cut ∧ cut ≤ b.right.val) : a = b := by
  by_contra hne
  rcases exterior_separated m ha hb hne with hs | hs
  · have : a.right.val < b.left.val := hs
    omega
  · have : b.right.val < a.left.val := hs
    omega

/-- A nonempty active stack has an exterior bottom arch crossing the cut. -/
theorem exists_exterior_through {n cut : Nat} (m : NoncrossingMatching n)
    (hne : (m.active cut).Nonempty) :
    ∃ a ∈ m.exteriorArches, a.left.val < cut ∧ cut ≤ a.right.val := by
  let u := (m.active cut).min' hne
  have hu : u ∈ m.active cut := Finset.min'_mem _ _
  have hum := m.mem_active.mp hu
  have hup : u < m.partner u := by change u.val < (m.partner u).val; omega
  have hus : m.wordOf[u.val]? = some U := by
    rw [m.getElem?_wordOf u.isLt, m.partnerIndex_coe]
    simp [hup]
  let a := m.archAt u
  have hal : a.left = u := archAt_left_of_U m u hus
  have har : a.right = m.partner u := by
    rw [← hal, m.partner_left (m.archAt_mem u)]
  refine ⟨a, ?_, by simpa [hal, har] using hum⟩
  rw [m.mem_exteriorArches_iff_active_empty (m.archAt_mem u), hal]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hvm := m.mem_active.mp hv
  have hvc : v ∈ m.active cut := by
    rw [m.mem_active]
    refine ⟨by omega, ?_⟩
    by_contra hbad
    have hnevu : m.partner v ≠ u := by
      intro he
      have := congrArg m.partner he
      simp only [m.partner_partner] at this
      have hlt : v.val < u.val := hvm.1
      rw [← this] at hup
      exact (not_lt_of_ge (le_of_lt hup)) hlt
    have hltvu : u < m.partner v := lt_of_le_of_ne hvm.2 hnevu.symm
    exact m.not_interleave rfl rfl hvm.1 hltvu (by
      change (m.partner v).val < (m.partner u).val
      omega)
  have hmin : u ≤ v := Finset.min'_le _ _ hvc
  exact (not_lt_of_ge hmin) hvm.1

/-- Right inward letters are the complemented original letters at reflected indices. -/
theorem getElem_reverseComplement {w : List DyckStep} {i : Nat} (hi : i < w.length) :
    (Dyck.reverseComplement w)[i]? = (w[w.length - 1 - i]?).map Dyck.complement := by
  rw [Dyck.reverseComplement, List.getElem?_map, List.getElem?_reverse hi]

/-- A right inward return event is an original exterior opener. -/
theorem right_return_iff {n cut i : Nat} (m : NoncrossingMatching n)
    (hi : i < 2 * n - cut) :
    (Dyck.reverseComplement (m.wordOf.drop cut))[i]? = some D ∧
        Meanders.height (Dyck.reverseComplement (m.wordOf.drop cut)) i = 1 ↔
      m.wordOf[2 * n - 1 - i]? = some U ∧
        Meanders.height m.wordOf (2 * n - 1 - i) = 0 := by
  have hc : cut ≤ 2 * n := by omega
  have he : Dyck.reverseComplement (m.wordOf.drop cut) =
      (Dyck.reverseComplement m.wordOf).take (2 * n - cut) := by
    rw [Dyck.take_reverseComplement, m.length_wordOf, Nat.sub_sub_self hc]
  rw [he, returnEvent_take_iff hi,
    getElem_reverseComplement (by simp only [m.length_wordOf]; omega),
    height_reverse_prefix (Balanced.of_isDyck m.isDyck_wordOf), m.length_wordOf]
  have heq : 2 * n - i = (2 * n - 1 - i) + 1 := by omega
  rw [heq]
  have hj : 2 * n - 1 - i < 2 * n := by omega
  rcases getElem?_eq_U_or_D (w := m.wordOf) (by simpa using hj) with hu | hd
  · rw [height_succ_of_U hu, hu]
    simp only [Option.map_some, Dyck.complement_U, true_and]
    omega
  · rw [hd]
    simp

/-- The original matching has an exterior arch through a cut exactly when its
original height is positive, including either endpoint cut. -/
theorem exterior_through_iff {n cut : Nat} (m : NoncrossingMatching n)
    (hc : cut ≤ 2 * n) :
    (∃ a ∈ m.exteriorArches, a.left.val < cut ∧ cut ≤ a.right.val) ↔
      0 < Meanders.height m.wordOf cut := by
  rw [← m.card_active hc, Nat.cast_pos, Finset.card_pos]
  constructor
  · rintro ⟨a, ha, hl, hr⟩
    refine ⟨a.left, ?_⟩
    rw [m.mem_active, m.partner_left (m.mem_exteriorArches.mp ha).1]
    exact ⟨hl, hr⟩
  · exact exists_exterior_through m

/-- The left and physically reflected right return events, plus the possible
unique exterior arch crossing the cut. -/
abbrev CutEvent {n : Nat} (m : NoncrossingMatching n) (cut : Nat) :=
  ReturnEvent (m.wordOf.take cut) ⊕
    ReturnEvent (Dyck.reverseComplement (m.wordOf.drop cut)) ⊕
      {_u : Unit // 0 < Meanders.height m.wordOf cut}

private theorem left_index_bound {n cut : Nat} (m : NoncrossingMatching n)
    (e : ReturnEvent (m.wordOf.take cut)) : e.val.val < cut ∧ e.val.val < 2 * n := by
  have := e.val.isLt
  simp only [List.length_take, m.length_wordOf] at this
  omega

private def leftEventArch {n cut : Nat} (m : NoncrossingMatching n)
    (e : ReturnEvent (m.wordOf.take cut)) : {a // a ∈ m.exteriorArches} := by
  let v : Point n := ⟨e.val.val, (left_index_bound m e).2⟩
  have he := (returnEvent_take_iff (left_index_bound m e).1).mp e.property
  have hr := archAt_right_of_D m v he.1
  exact ⟨m.archAt v, (exterior_iff_closer_height_one m (m.archAt_mem v)).mpr
    (by rw [hr]; exact he.2)⟩

private theorem leftEventArch_right {n cut : Nat} (m : NoncrossingMatching n)
    (e : ReturnEvent (m.wordOf.take cut)) : (leftEventArch m e).val.right.val = e.val.val := by
  exact congrArg Fin.val (archAt_right_of_D m _
    ((returnEvent_take_iff (left_index_bound m e).1).mp e.property).1)

private theorem right_index_bound {n cut : Nat} (m : NoncrossingMatching n)
    (e : ReturnEvent (Dyck.reverseComplement (m.wordOf.drop cut))) :
    e.val.val < 2 * n - cut := by
  simpa only [Dyck.reverseComplement_length, List.length_drop, m.length_wordOf]
    using e.val.isLt

private def rightEventArch {n cut : Nat} (m : NoncrossingMatching n)
    (e : ReturnEvent (Dyck.reverseComplement (m.wordOf.drop cut))) :
    {a // a ∈ m.exteriorArches} := by
  have hi := right_index_bound m e
  let v : Point n := ⟨2 * n - 1 - e.val.val, by omega⟩
  have he := (right_return_iff m hi).mp e.property
  have hl := archAt_left_of_U m v he.1
  exact ⟨m.archAt v, (exterior_iff_opener_height_zero m (m.archAt_mem v)).mpr
    (by rw [hl]; exact he.2)⟩

private theorem rightEventArch_left {n cut : Nat} (m : NoncrossingMatching n)
    (e : ReturnEvent (Dyck.reverseComplement (m.wordOf.drop cut))) :
    (rightEventArch m e).val.left.val = 2 * n - 1 - e.val.val := by
  exact congrArg Fin.val (archAt_left_of_U m _
    ((right_return_iff m (right_index_bound m e)).mp e.property).1)

private noncomputable def throughEventArch {n cut : Nat} (m : NoncrossingMatching n)
    (hc : cut ≤ 2 * n) (e : {_u : Unit // 0 < Meanders.height m.wordOf cut}) :
    {a // a ∈ m.exteriorArches} :=
  ⟨((exterior_through_iff m hc).mpr e.property).choose,
    ((exterior_through_iff m hc).mpr e.property).choose_spec.1⟩

private theorem throughEventArch_crosses {n cut : Nat} (m : NoncrossingMatching n)
    (hc : cut ≤ 2 * n) (e : {_u : Unit // 0 < Meanders.height m.wordOf cut}) :
    (throughEventArch m hc e).val.left.val < cut ∧
      cut ≤ (throughEventArch m hc e).val.right.val :=
  ((exterior_through_iff m hc).mpr e.property).choose_spec.2

/-- Reconstruct the marked arch from its original half event or through choice. -/
noncomputable def cutEventArch {n cut : Nat} (m : NoncrossingMatching n)
    (hc : cut ≤ 2 * n) : CutEvent m cut → {a // a ∈ m.exteriorArches}
  | .inl e => leftEventArch m e
  | .inr (.inl e) => rightEventArch m e
  | .inr (.inr e) => throughEventArch m hc e

private theorem cutEventArch_injective {n cut : Nat} (m : NoncrossingMatching n)
    (hc : cut ≤ 2 * n) : Function.Injective (cutEventArch m hc) := by
  intro x y he
  have hl := congrArg (fun a => a.val.left.val) he
  have hr := congrArg (fun a => a.val.right.val) he
  rcases x with x | x <;> rcases y with y | y
  · congr 1
    apply Subtype.ext
    apply Fin.ext
    exact (leftEventArch_right m x).symm.trans (hr.trans (leftEventArch_right m y))
  · rcases y with y | y
    · have hx := left_index_bound m x
      have hy := right_index_bound m y
      have hxl := (leftEventArch m x).val.ordered
      have hyr := (rightEventArch m y).val.ordered
      have hxr := leftEventArch_right m x
      have hyl := rightEventArch_left m y
      change (leftEventArch m x).val.left.val = (rightEventArch m y).val.left.val at hl
      change (leftEventArch m x).val.right.val = (rightEventArch m y).val.right.val at hr
      simp only [Fin.lt_def] at hxl hyr
      omega
    · have hx := left_index_bound m x
      have hy := throughEventArch_crosses m hc y
      have hxr := leftEventArch_right m x
      change (leftEventArch m x).val.right.val = (throughEventArch m hc y).val.right.val at hr
      omega
  · rcases x with x | x
    · have hx := right_index_bound m x
      have hy := left_index_bound m y
      have hyl := (leftEventArch m y).val.ordered
      have hxl := rightEventArch_left m x
      have hyr := leftEventArch_right m y
      change (rightEventArch m x).val.left.val = (leftEventArch m y).val.left.val at hl
      simp only [Fin.lt_def] at hyl
      omega
    · have hx := throughEventArch_crosses m hc x
      have hy := left_index_bound m y
      have hyr := leftEventArch_right m y
      change (throughEventArch m hc x).val.right.val = (leftEventArch m y).val.right.val at hr
      omega
  · rcases x with x | x <;> rcases y with y | y
    · congr 2
      apply Subtype.ext
      apply Fin.ext
      have hx := right_index_bound m x
      have hy := right_index_bound m y
      change (rightEventArch m x).val.left.val = (rightEventArch m y).val.left.val at hl
      rw [rightEventArch_left, rightEventArch_left] at hl
      omega
    · have hx := right_index_bound m x
      have hy := throughEventArch_crosses m hc y
      have hxl := rightEventArch_left m x
      change (rightEventArch m x).val.left.val = (throughEventArch m hc y).val.left.val at hl
      omega
    · have hx := throughEventArch_crosses m hc x
      have hy := right_index_bound m y
      have hyl := rightEventArch_left m y
      change (throughEventArch m hc x).val.left.val = (rightEventArch m y).val.left.val at hl
      omega
    · congr 2
      exact Subsingleton.elim _ _

private theorem cutEventArch_surjective {n cut : Nat} (m : NoncrossingMatching n)
    (hc : cut ≤ 2 * n) : Function.Surjective (cutEventArch m hc) := by
  intro a
  have ha := (m.mem_exteriorArches.mp a.property).1
  by_cases hr : a.val.right.val < cut
  · let e : ReturnEvent (m.wordOf.take cut) :=
      ⟨⟨a.val.right.val, by
          simp only [List.length_take, m.length_wordOf]
          exact lt_min hr a.val.right.isLt⟩,
        (returnEvent_take_iff hr).mpr
          ⟨(m.paired_wordOf ha).isD, (exterior_iff_closer_height_one m ha).mp a.property⟩⟩
    refine ⟨.inl e, ?_⟩
    apply Subtype.ext
    change m.archAt ⟨a.val.right.val, _⟩ = a.val
    exact m.archAt_right ha
  · by_cases hl : cut ≤ a.val.left.val
    · have hj : 2 * n - 1 - a.val.left.val < 2 * n - cut := by
        have := a.val.left.isLt
        omega
      have heq : 2 * n - 1 - (2 * n - 1 - a.val.left.val) = a.val.left.val := by
        have := a.val.left.isLt
        omega
      let e : ReturnEvent (Dyck.reverseComplement (m.wordOf.drop cut)) :=
        ⟨⟨2 * n - 1 - a.val.left.val, by
          simpa only [Dyck.reverseComplement_length, List.length_drop,
            m.length_wordOf] using hj⟩,
          (right_return_iff m hj).mpr (by rw [heq]; exact
            ⟨(m.paired_wordOf ha).isU,
              (exterior_iff_opener_height_zero m ha).mp a.property⟩)⟩
      refine ⟨.inr (.inl e), ?_⟩
      apply Subtype.ext
      apply m.archAt_eq ha
      exact Or.inl (Fin.ext heq)
    · have hac : a.val.left.val < cut ∧ cut ≤ a.val.right.val := by omega
      let e : {_u : Unit // 0 < Meanders.height m.wordOf cut} :=
        ⟨(), (exterior_through_iff m hc).mp ⟨a.val, a.property, hac⟩⟩
      refine ⟨.inr (.inr e), ?_⟩
      apply Subtype.ext
      exact exterior_through_unique m (throughEventArch m hc e).property a.property
        (throughEventArch_crosses m hc e) hac

/-- The marking bijection precedes the counting identity: every exterior arch
is exactly one left return, one reflected right return, or the unique through
arch. The event sets inspect actual original half-word steps and heights. -/
noncomputable def exteriorArchCutEquiv {n cut : Nat}
    (m : NoncrossingMatching n) (hc : cut ≤ 2 * n) :
    {a // a ∈ m.exteriorArches} ≃ CutEvent m cut :=
  (Equiv.ofBijective (cutEventArch m hc)
    ⟨cutEventArch_injective m hc, cutEventArch_surjective m hc⟩).symm

/-- The exact lower observer identity at any physical cut. -/
theorem exteriorCount_cut {n cut : Nat} (m : NoncrossingMatching n)
    (hc : cut ≤ 2 * n) :
    m.exteriorArches.card =
      Fintype.card (ReturnEvent (m.wordOf.take cut)) +
      Fintype.card (ReturnEvent (Dyck.reverseComplement (m.wordOf.drop cut))) +
      if 0 < Meanders.height m.wordOf cut then 1 else 0 := by
  classical
  have hc' := Fintype.card_congr (exteriorArchCutEquiv m hc)
  change _ = Fintype.card (ReturnEvent (m.wordOf.take cut) ⊕
    ReturnEvent (Dyck.reverseComplement (m.wordOf.drop cut)) ⊕
      {_u : Unit // 0 < Meanders.height m.wordOf cut}) at hc'
  rw [Fintype.card_coe, Fintype.card_sum, Fintype.card_sum] at hc'
  by_cases hp : 0 < Meanders.height m.wordOf cut
  · simpa [hp, Nat.add_assoc] using hc'
  · simpa [hp, Nat.add_assoc] using hc'

/-- Physical matching reflection reads the reverse-complement word. -/
theorem wordOf_reflect {n : Nat} (m : NoncrossingMatching n) :
    m.reflect.wordOf = Dyck.reverseComplement m.wordOf := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 2 * n
  · rw [m.reflect.getElem?_wordOf hi,
      getElem_reverseComplement (by simpa using hi), m.length_wordOf,
      m.getElem?_wordOf (by omega), m.partnerIndex_reflect hi]
    have hj : 2 * n - 1 - i < 2 * n := by omega
    have hpn := m.partnerIndex_ne hj
    have hpb := m.partnerIndex_lt hj
    by_cases hp : 2 * n - 1 - i < m.partnerIndex (2 * n - 1 - i)
    · have hr : ¬ i < 2 * n - 1 - m.partnerIndex (2 * n - 1 - i) := by omega
      simp [hp, hr]
    · have hr : i < 2 * n - 1 - m.partnerIndex (2 * n - 1 - i) := by omega
      simp [hp, hr]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi),
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hi)]

/-- Reflection exchanges the actual inward halves and preserves the cut height. -/
theorem reflected_cut_halves {n cut : Nat} (m : NoncrossingMatching n)
    (hc : cut ≤ 2 * n) :
    m.reflect.wordOf.take (2 * n - cut) = Dyck.reverseComplement (m.wordOf.drop cut) ∧
    Dyck.reverseComplement (m.reflect.wordOf.drop (2 * n - cut)) = m.wordOf.take cut ∧
    Meanders.height m.reflect.wordOf (2 * n - cut) = Meanders.height m.wordOf cut := by
  rw [wordOf_reflect]
  refine ⟨?_, ?_, ?_⟩
  · rw [Dyck.take_reverseComplement, m.length_wordOf, Nat.sub_sub_self hc]
  · simpa only [Dyck.reverseComplement_reverseComplement,
      Dyck.reverseComplement_length, m.length_wordOf] using
        (Dyck.take_reverseComplement (Dyck.reverseComplement m.wordOf) cut).symm
  · rw [height_reverse_prefix (Balanced.of_isDyck m.isDyck_wordOf),
      m.length_wordOf, Nat.sub_sub_self hc]

/-- Physical reflection reverses and mirrors the ordered arch endpoints. -/
def reflectArch {n : Nat} (a : Arch n) : Arch n :=
  ⟨a.right.mirror, a.left.mirror, Point.mirror_lt_mirror.mpr a.ordered⟩

@[simp] theorem reflectArch_reflectArch {n : Nat} (a : Arch n) :
    reflectArch (reflectArch a) = a := by
  apply Arch.ext <;> exact Point.mirror_mirror _

@[simp] theorem reflectArch_mem {n : Nat} (m : NoncrossingMatching n) (a : Arch n) :
    reflectArch a ∈ m.reflect.arches ↔ a ∈ m.arches := by
  rw [m.reflect.mem_arches_iff]
  change m.reflect.partner a.right.mirror = a.left.mirror ↔ a ∈ m.arches
  rw [m.partner_reflect, Point.mirror_mirror]
  constructor
  · intro he
    have hp := Point.mirror_injective he
    rw [m.mem_arches_iff]
    rw [← hp, m.partner_partner]
  · intro ha
    rw [m.partner_right ha]

private theorem reflectArch_encloses {n : Nat} (a b : Arch n) :
    (reflectArch a).ProperlyEncloses (reflectArch b) ↔ a.ProperlyEncloses b := by
  simp only [Arch.ProperlyEncloses, reflectArch, Point.mirror_lt_mirror, and_comm]

/-- Reflection transports exteriority by transporting enclosing arches. -/
theorem reflectArch_exterior {n : Nat} (m : NoncrossingMatching n) (a : Arch n) :
    reflectArch a ∈ m.reflect.exteriorArches ↔ a ∈ m.exteriorArches := by
  simp only [NoncrossingMatching.mem_exteriorArches, reflectArch_mem]
  constructor
  · rintro ⟨ha, hex⟩
    refine ⟨ha, fun b hb hen => ?_⟩
    exact hex (reflectArch b) ((reflectArch_mem m b).mpr hb)
      ((reflectArch_encloses b a).mpr hen)
  · rintro ⟨ha, hex⟩
    refine ⟨ha, fun b hb hen => ?_⟩
    have hb' : reflectArch b ∈ m.arches := by
      simpa only [NoncrossingMatching.reflect_reflect] using
        (reflectArch_mem m.reflect b).mpr hb
    apply hex (reflectArch b) hb'
    rw [← reflectArch_encloses, reflectArch_reflectArch]
    exact hen

/-- The marked physical arch reflection, with explicit endpoint action. -/
def exteriorReflectionEquiv {n : Nat} (m : NoncrossingMatching n) :
    {a // a ∈ m.exteriorArches} ≃ {a // a ∈ m.reflect.exteriorArches} where
  toFun a := ⟨reflectArch a.val, (reflectArch_exterior m a.val).mpr a.property⟩
  invFun a := ⟨reflectArch a.val, by
    simpa only [NoncrossingMatching.reflect_reflect] using
      (reflectArch_exterior m.reflect a.val).mpr a.property⟩
  left_inv a := Subtype.ext (reflectArch_reflectArch a.val)
  right_inv a := Subtype.ext (reflectArch_reflectArch a.val)

@[simp] theorem exteriorReflectionEquiv_left {n : Nat} (m : NoncrossingMatching n)
    (a : {a // a ∈ m.exteriorArches}) :
    (exteriorReflectionEquiv m a).val.left = a.val.right.mirror := rfl

@[simp] theorem exteriorReflectionEquiv_right {n : Nat} (m : NoncrossingMatching n)
    (a : {a // a ∈ m.exteriorArches}) :
    (exteriorReflectionEquiv m a).val.right = a.val.left.mirror := rfl

/-- Word equality transports an event without changing its original index. -/
def returnEventCast {a b : List DyckStep} (h : a = b) : ReturnEvent a ≃ ReturnEvent b :=
  Equiv.cast (congrArg ReturnEvent h)

@[simp] theorem returnEventCast_index {a b : List DyckStep} (h : a = b)
    (e : ReturnEvent a) : (returnEventCast h e).val.val = e.val.val := by
  subst b
  rfl

/-- Reflection swaps the return classes at the same inward index and maps
through marks to through marks. The word casts are the actual half exchange. -/
def reflectCutEvent {n cut : Nat} (m : NoncrossingMatching n) (hc : cut ≤ 2 * n) :
    CutEvent m cut → CutEvent m.reflect (2 * n - cut)
  | .inl e => .inr (.inl (returnEventCast (reflected_cut_halves m hc).2.1.symm e))
  | .inr (.inl e) => .inl (returnEventCast (reflected_cut_halves m hc).1.symm e)
  | .inr (.inr e) => .inr (.inr ⟨e.val, by
      rw [(reflected_cut_halves m hc).2.2]
      exact e.property⟩)

/-- The event-class exchange commutes with physical arch reflection. This
identifies the marked arch, not merely the two total observer counts. -/
theorem exteriorCut_reflection {n cut : Nat} (m : NoncrossingMatching n)
    (hc : cut ≤ 2 * n) (e : CutEvent m cut) :
    exteriorReflectionEquiv m (cutEventArch m hc e) =
      cutEventArch m.reflect (by omega) (reflectCutEvent m hc e) := by
  apply Subtype.ext
  have hmem := (m.reflect.mem_exteriorArches.mp
    (exteriorReflectionEquiv m (cutEventArch m hc e)).property).1
  have hmem' := (m.reflect.mem_exteriorArches.mp
    (cutEventArch m.reflect (by omega) (reflectCutEvent m hc e)).property).1
  rcases e with e | e
  · apply m.reflect.eq_of_contains hmem hmem' (Arch.contains_left _)
    apply Or.inl
    apply Fin.ext
    change (leftEventArch m e).val.right.mirror.val =
      (rightEventArch m.reflect
        (returnEventCast (reflected_cut_halves m hc).2.1.symm e)).val.left.val
    rw [Point.mirror_val, leftEventArch_right, rightEventArch_left, returnEventCast_index]
  · rcases e with e | e
    · apply m.reflect.eq_of_contains hmem hmem' (Arch.contains_right _)
      apply Or.inr
      apply Fin.ext
      change (rightEventArch m e).val.left.mirror.val =
        (leftEventArch m.reflect
          (returnEventCast (reflected_cut_halves m hc).1.symm e)).val.right.val
      rw [Point.mirror_val, rightEventArch_left, leftEventArch_right, returnEventCast_index]
      have := right_index_bound m e
      omega
    · apply exterior_through_unique m.reflect
        (exteriorReflectionEquiv m (cutEventArch m hc (.inr (.inr e)))).property
        (cutEventArch m.reflect (by omega)
          (reflectCutEvent m hc (.inr (.inr e)))).property
      · have he := throughEventArch_crosses m hc e
        change (throughEventArch m hc e).val.right.mirror.val < 2 * n - cut ∧
          2 * n - cut ≤ (throughEventArch m hc e).val.left.mirror.val
        rw [Point.mirror_val, Point.mirror_val]
        have hl := (throughEventArch m hc e).val.left.isLt
        have hr := (throughEventArch m hc e).val.right.isLt
        omega
      · exact throughEventArch_crosses m.reflect (by omega)
          ⟨e.val, by rw [(reflected_cut_halves m hc).2.2]; exact e.property⟩

end Meanders.FirstCrossing
