import Meanders.Models.FirstCrossing.Native.State
import Meanders.Core.Graph.Pairing
import Meanders.Core.Matching.Prefix

/-!
# Exact raw pairing codec and cyclic stack checking

Raw mate validation gives a fixed-point-free involution and an even domain.
The stack check is proved equivalent to noncrossing after any explicit cyclic
permutation: soundness tracks exactly the open original arches, and completeness
reuses the existing matching stack equations. The concrete four-group cyclic
list is a permutation of the storage domain, so every validated native key
decodes to a canonical geometric matching and re-encodes to its exact mate list.
-/

namespace Meanders.FirstCrossing

/-- Raw validation rejects precisely failure of the mate involution or a fixed point. -/
theorem pairingValid_iff (mate : List Nat) :
    pairingValid mate = true ↔ ∀ i, i < mate.length →
      ∃ j, mate[i]? = some j ∧ i ≠ j ∧ mate[j]? = some i := by
  simp only [pairingValid, List.all_eq_true, List.mem_range]
  constructor
  · intro h i hi
    have hh := h i hi
    cases he : mate[i]? with
    | none => simp [he] at hh
    | some j => exact ⟨j, rfl, by simpa [he] using hh⟩
  · intro h i hi
    obtain ⟨j, hj, hne, hji⟩ := h i hi
    simp [hj, hne, hji]

/-- Every validated stored mate is itself a port in the same exact domain. -/
theorem pairingValid_bound {mate : List Nat} (h : pairingValid mate = true)
    {i : Nat} (hi : i < mate.length) : mate[i] < mate.length := by
  obtain ⟨j, hj, _, hji⟩ := (pairingValid_iff mate).mp h i hi
  have he : mate[i] = j := by simpa [List.getElem?_eq_getElem hi] using hj
  rw [he]
  exact List.getElem?_eq_some_iff.mp hji |>.1

/-- Exact decoding of the raw list to a finite-domain partner function. -/
def rawPartner (mate : List Nat) (h : pairingValid mate = true) :
    Fin mate.length → Fin mate.length :=
  fun i => ⟨mate[i.val], pairingValid_bound h i.isLt⟩

@[simp] theorem rawPartner_val (mate : List Nat) (h : pairingValid mate = true)
    (i : Fin mate.length) : (rawPartner mate h i).val = mate[i.val] := rfl

private theorem pairingValid_lookup {mate : List Nat} (h : pairingValid mate = true)
    {i : Nat} (hi : i < mate.length) : i ≠ mate[i] ∧ mate[mate[i]]? = some i := by
  obtain ⟨j, hj, hne, hji⟩ := (pairingValid_iff mate).mp h i hi
  have he : mate[i] = j := by simpa only [List.getElem?_eq_getElem hi, Option.some.injEq] using hj
  simpa only [he] using And.intro hne hji

/-- Validation is sufficient for involution; no noncrossing assumption is hidden here. -/
theorem rawPartner_involutive (mate : List Nat) (h : pairingValid mate = true) :
    Function.Involutive (rawPartner mate h) := by
  intro i
  apply Fin.ext
  have he := (pairingValid_lookup h i.isLt).2
  have hb := pairingValid_bound h i.isLt
  change mate[mate[i.val]] = i.val
  simpa only [List.getElem?_eq_getElem (pairingValid_bound h i.isLt), Option.some.injEq]
    using he

/-- Validation excludes fixed ports. -/
theorem rawPartner_ne (mate : List Nat) (h : pairingValid mate = true)
    (i : Fin mate.length) : rawPartner mate h i ≠ i := by
  intro he
  exact (pairingValid_lookup h i.isLt).1 (congrArg Fin.val he).symm

/-- The raw domain is necessarily even: the port rank need not be assumed. -/
theorem pairingValid_even_length {mate : List Nat} (h : pairingValid mate = true) :
    Even mate.length := by
  have he := even_card_of_pairing (Finset.univ : Finset (Fin mate.length))
    (rawPartner mate h) (by simp) (fun i _ => rawPartner_involutive mate h i)
    (fun i _ => rawPartner_ne mate h i)
  simpa only [Finset.card_univ, Fintype.card_fin] using he

/-- An explicit cyclic ordering relabels storage ports without identifying owners. -/
def cyclicPartner {n : Nat} (mate : List Nat) (h : pairingValid mate = true)
    (order : Point n ≃ Fin mate.length) : Point n → Point n :=
  fun i => order.symm (rawPartner mate h (order i))

/-- The cyclic partner remains an involution under the exact permutation. -/
theorem cyclicPartner_involutive {n : Nat} (mate : List Nat) (h : pairingValid mate = true)
    (order : Point n ≃ Fin mate.length) : Function.Involutive (cyclicPartner mate h order) := by
  intro i
  simp only [cyclicPartner, Equiv.apply_symm_apply]
  rw [rawPartner_involutive mate h, Equiv.symm_apply_apply]

/-- No permutation can introduce a fixed point in the pairing. -/
theorem cyclicPartner_ne {n : Nat} (mate : List Nat) (h : pairingValid mate = true)
    (order : Point n ≃ Fin mate.length) (i : Point n) : cyclicPartner mate h order i ≠ i := by
  intro he
  apply rawPartner_ne mate h (order i)
  have hp := congrArg order he
  simpa only [cyclicPartner, Equiv.apply_symm_apply] using hp

/-- The semantic planar condition on the original cyclic index order. It is
separate from involution validity and from a Boolean stack-check report. -/
def CyclicNoncrossing {n : Nat} (mate : List Nat) (h : pairingValid mate = true)
    (order : Point n ≃ Fin mate.length) : Prop :=
  ∀ i j, i < j → j < cyclicPartner mate h order i →
    cyclicPartner mate h order i < cyclicPartner mate h order j → False

/-- Decode an actual planar raw pairing through the existing partner constructor. -/
def matchingOfRaw {n : Nat} (mate : List Nat) (h : pairingValid mate = true)
    (order : Point n ≃ Fin mate.length) (hp : CyclicNoncrossing mate h order) :
    NoncrossingMatching n :=
  NoncrossingMatching.ofPartner (cyclicPartner mate h order)
    ⟨cyclicPartner_involutive mate h order, cyclicPartner_ne mate h order, hp⟩

/-- The decoded geometric partner is exactly the conjugated stored mate. -/
@[simp] theorem partner_matchingOfRaw {n : Nat} (mate : List Nat)
    (h : pairingValid mate = true) (order : Point n ≃ Fin mate.length)
    (hp : CyclicNoncrossing mate h order) (i : Point n) :
    (matchingOfRaw mate h order hp).partner i = cyclicPartner mate h order i :=
  NoncrossingMatching.partner_ofPartner _ _ _

/-- Decoding preserves the original storage mate at every port. -/
theorem matchingOfRaw_storage_partner {n : Nat} (mate : List Nat)
    (h : pairingValid mate = true) (order : Point n ≃ Fin mate.length)
    (hp : CyclicNoncrossing mate h order) (i : Fin mate.length) :
    order ((matchingOfRaw mate h order hp).partner (order.symm i)) = rawPartner mate h i := by
  simp only [partner_matchingOfRaw, cyclicPartner, Equiv.apply_symm_apply]

/-- Encoding writes exactly one partner index per storage port. -/
def encodeMatching {n size : Nat} (m : NoncrossingMatching n)
    (order : Point n ≃ Fin size) : List Nat :=
  List.ofFn fun i => (order (m.partner (order.symm i))).val

@[simp] theorem length_encodeMatching {n size : Nat} (m : NoncrossingMatching n)
    (order : Point n ≃ Fin size) : (encodeMatching m order).length = size := by
  simp only [encodeMatching, List.length_ofFn]

theorem getElem?_encodeMatching {n size i : Nat} (m : NoncrossingMatching n)
    (order : Point n ≃ Fin size) (hi : i < size) :
    (encodeMatching m order)[i]? = some (order (m.partner (order.symm ⟨i, hi⟩))).val := by
  simp only [encodeMatching, List.getElem?_ofFn, dite_eq_left hi]

/-- Re-encoding after planar decoding recovers every original storage byte. -/
theorem encodeMatching_matchingOfRaw {n : Nat} (mate : List Nat)
    (h : pairingValid mate = true) (order : Point n ≃ Fin mate.length)
    (hp : CyclicNoncrossing mate h order) :
    encodeMatching (matchingOfRaw mate h order hp) order = mate := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < mate.length
  · rw [getElem?_encodeMatching _ _ hi, matchingOfRaw_storage_partner]
    exact (List.getElem?_eq_getElem hi).symm
  · rw [List.getElem?_eq_none (by simpa only [length_encodeMatching] using le_of_not_gt hi),
      List.getElem?_eq_none (le_of_not_gt hi)]

/-- An accepted stack is a subsequence of the remaining physical endpoints.
A missing or already-consumed expected closer can never disappear silently. -/
theorem cyclicCheck_stack_sublist (mate : List (Option Nat)) (xs stack : List Nat)
    (h : cyclicCheck mate xs stack = true) : stack.Sublist xs := by
  induction xs generalizing stack with
  | nil =>
      have he : stack = [] := by simpa only [cyclicCheck, List.isEmpty_iff] using h
      simp only [he, List.Sublist.refl]
  | cons x xs ih =>
      cases stack with
      | nil => exact List.nil_sublist _
      | cons y ys =>
          simp only [cyclicCheck] at h
          by_cases he : x = y
          · subst x
            simp only [beq_self_eq_true, ite_true] at h
            exact List.Sublist.cons_cons y (ih ys h)
          · have hb : (x == y) = false := by simp [he]
            simp only [hb, Bool.false_eq_true, ite_false] at h
            cases hm : (mate[x]?).join with
            | none => simp only [hm, Bool.false_eq_true] at h
            | some z =>
                rw [hm] at h
                exact (List.sublist_cons_self z (y :: ys)).trans ((ih _ h).trans
                  (List.sublist_cons_self x xs))

/-- Natural-index mate lookup, fixing positions outside the raw domain. -/
def mateIndex (mate : List Nat) (i : Nat) : Nat := (mate[i]?).getD i

@[simp] theorem mateIndex_eq {mate : List Nat} {i : Nat} (hi : i < mate.length) :
    mateIndex mate i = mate[i] := by simp only [mateIndex, List.getElem?_eq_getElem hi,
      Option.getD_some]

theorem mateIndex_lt {mate : List Nat} (h : pairingValid mate = true)
    {i : Nat} (hi : i < mate.length) : mateIndex mate i < mate.length := by
  rw [mateIndex_eq hi]
  exact pairingValid_bound h hi

theorem mateIndex_involutive {mate : List Nat} (h : pairingValid mate = true)
    {i : Nat} (hi : i < mate.length) : mateIndex mate (mateIndex mate i) = i := by
  rw [mateIndex_eq hi, mateIndex, (pairingValid_lookup h hi).2]
  rfl

private theorem cyclicCheck_step {mate : List Nat} {t : Nat} (ht : t < mate.length)
    {xs stack : List Nat} (h : cyclicCheck (mate.map some) (t :: xs) stack = true) :
    (∃ ys, stack = t :: ys ∧ cyclicCheck (mate.map some) xs ys = true) ∨
      cyclicCheck (mate.map some) xs (mateIndex mate t :: stack) = true := by
  have hm : ((mate.map some)[t]?).join = some (mateIndex mate t) := by
    simp only [List.getElem?_map, List.getElem?_eq_getElem ht, Option.map_some,
      Option.join_some, mateIndex_eq ht]
  cases stack with
  | nil => exact Or.inr (by simpa only [cyclicCheck, hm] using h)
  | cons x xs' =>
      by_cases he : t = x
      · subst x
        exact Or.inl ⟨xs', rfl, by simpa only [cyclicCheck, beq_self_eq_true,
          ite_true] using h⟩
      · have hb : (t == x) = false := by simp [he]
        simp only [cyclicCheck, hb, Bool.false_eq_true, ite_false, hm] at h
        exact Or.inr h

/-- Exact open-arch frontier for the chronological cyclic scan. -/
private def ScanStack (mate : List Nat) (t : Nat) (stack : List Nat) : Prop :=
  ∀ j, j ∈ stack ↔ t ≤ j ∧ j < mate.length ∧ mateIndex mate j < t

private theorem scanStack_pop {mate : List Nat} (h : pairingValid mate = true)
    {t : Nat} {ys : List Nat} (hs : ScanStack mate t (t :: ys))
    (hn : t ∉ ys) : ScanStack mate (t + 1) ys := by
  have ht := (hs t).mp (List.mem_cons_self ..)
  intro j
  have hold := hs j
  constructor
  · intro hj
    have ho := hold.mp (List.mem_cons_of_mem _ hj)
    have hne : j ≠ t := by intro he; subst j; exact hn hj
    exact ⟨by omega, ho.2.1, by omega⟩
  · rintro ⟨hj, hjb, hpj⟩
    have hne : mateIndex mate j ≠ t := by
      intro he
      have hinv := mateIndex_involutive h hjb
      rw [he] at hinv
      omega
    have hmem := hold.mpr ⟨by omega, hjb, by omega⟩
    exact (List.mem_cons.mp hmem).resolve_left (by omega)

private theorem scanStack_push {mate : List Nat} (h : pairingValid mate = true)
    {t : Nat} {stack : List Nat} (ht : t < mate.length) (hs : ScanStack mate t stack)
    (hfuture : t < mateIndex mate t) :
    ScanStack mate (t + 1) (mateIndex mate t :: stack) := by
  intro j
  rw [List.mem_cons, hs j]
  have hft := mateIndex_lt h ht
  have hinv := mateIndex_involutive h ht
  constructor
  · rintro (rfl | ⟨hj, hjb, hfj⟩)
    · exact ⟨by omega, hft, by omega⟩
    · have hne : j ≠ t := by intro he; subst j; omega
      exact ⟨by omega, hjb, by omega⟩
  · rintro ⟨hj, hjb, hfj⟩
    by_cases he : mateIndex mate j = t
    · have hi := mateIndex_involutive h hjb
      rw [he] at hi
      exact Or.inl hi.symm
    · exact Or.inr ⟨by omega, hjb, by omega⟩

private theorem cyclicCheck_no_cross_from {mate : List Nat} (h : pairingValid mate = true)
    (d : Nat) : ∀ t stack, t + d = mate.length → ScanStack mate t stack →
    cyclicCheck (mate.map some) (List.range' t d) stack = true →
    ∀ a b, a < mate.length → b < mate.length → a < b → t ≤ b →
      b < mateIndex mate a → mateIndex mate a < mateIndex mate b → False := by
  induction d with
  | zero => intro t stack ht hs hc a b ha hb hab htb hba hfab; omega
  | succ d ih =>
      intro t stack ht hs hc a b ha hb hab htb hba hfab
      rw [List.range'_succ] at hc
      have htt : t < mate.length := by omega
      rcases cyclicCheck_step htt hc with ⟨ys, rfl, htail⟩ | htail
      · have hsub := cyclicCheck_stack_sublist _ _ _ htail
        have hn : t ∉ ys := by
          intro hm
          have hx := List.mem_range'_1.mp (hsub.subset hm)
          omega
        have hs' := scanStack_pop h hs hn
        by_cases he : t = b
        · subst b
          have hft := (hs t).mp (List.mem_cons_self ..)
          omega
        · exact ih (t + 1) ys (by omega) hs' htail a b ha hb hab (by omega) hba hfab
      · have hsub := cyclicCheck_stack_sublist _ _ _ htail
        have hfuture : t < mateIndex mate t := by
          have hx := List.mem_range'_1.mp (hsub.subset (List.mem_cons_self ..))
          omega
        have hs' := scanStack_push h htt hs hfuture
        by_cases he : t = b
        · subst b
          have hm : mateIndex mate a ∈ stack := (hs _).mpr
            ⟨by omega, mateIndex_lt h ha, by rw [mateIndex_involutive h ha]; omega⟩
          have hpw := (List.pairwise_lt_range').sublist hsub
          have hlt := (List.pairwise_cons.mp hpw).1 (mateIndex mate a) hm
          omega
        · exact ih (t + 1) (mateIndex mate t :: stack) (by omega) hs' htail
            a b ha hb hab (by omega) hba hfab

/-- The actual Boolean stack checker forbids crossing partner intervals in
the scanned index order. This is semantic soundness, not a recheck postcondition. -/
theorem cyclicCheck_range_noncrossing {mate : List Nat} (h : pairingValid mate = true)
    (hc : cyclicCheck (mate.map some) (List.range mate.length) [] = true)
    {a b : Nat} (ha : a < mate.length) (hb : b < mate.length)
    (hab : a < b) (hba : b < mateIndex mate a)
    (hfab : mateIndex mate a < mateIndex mate b) : False := by
  apply cyclicCheck_no_cross_from h mate.length 0 [] (by omega) ?_ ?_
    a b ha hb hab (by omega) hba hfab
  · intro j
    simp only [List.not_mem_nil, false_iff, not_and]
    omega
  · simpa only [← List.range_eq_range'] using hc

/-- A bounded involution is written as one exact mate entry per port. -/
private theorem pairingValid_ofFn {size : Nat} (f : Fin size → Fin size)
    (hinv : Function.Involutive f) (hne : ∀ i, f i ≠ i) :
    pairingValid (List.ofFn fun i => (f i).val) = true := by
  rw [pairingValid_iff]
  intro i hi
  have hib : i < size := by simpa only [List.length_ofFn] using hi
  let v : Fin size := ⟨i, hib⟩
  refine ⟨(f v).val, ?_, ?_, ?_⟩
  · simp only [List.getElem?_ofFn, dite_eq_left hib]
    rfl
  · intro he
    exact hne v (Fin.ext he.symm)
  · rw [List.getElem?_ofFn, dite_eq_left (f v).isLt]
    change some (f (f v)).val = some i
    rw [hinv v]

/-- The same raw pairing, indexed by consecutive positions of its cyclic order. -/
def cyclicMate {n : Nat} (mate : List Nat) (h : pairingValid mate = true)
    (order : Point n ≃ Fin mate.length) : List Nat :=
  List.ofFn fun i => (cyclicPartner mate h order i).val

@[simp] theorem length_cyclicMate {n : Nat} (mate : List Nat)
    (h : pairingValid mate = true) (order : Point n ≃ Fin mate.length) :
    (cyclicMate mate h order).length = 2 * n := by simp only [cyclicMate, List.length_ofFn]

theorem pairingValid_cyclicMate {n : Nat} (mate : List Nat)
    (h : pairingValid mate = true) (order : Point n ≃ Fin mate.length) :
    pairingValid (cyclicMate mate h order) = true :=
  pairingValid_ofFn _ (cyclicPartner_involutive mate h order) (cyclicPartner_ne mate h order)

private theorem cyclicMate_lookup {n : Nat} (mate : List Nat)
    (h : pairingValid mate = true) (order : Point n ≃ Fin mate.length) (i : Point n) :
    ((cyclicMate mate h order).map some)[i.val]?.join =
      some (cyclicPartner mate h order i).val := by
  simp only [cyclicMate, List.getElem?_map, List.getElem?_ofFn, dite_eq_left i.isLt,
    Option.map_some, Option.join_some]

private theorem orderedMate_lookup {n : Nat} (mate : List Nat)
    (h : pairingValid mate = true) (order : Point n ≃ Fin mate.length) (i : Point n) :
    (mate.map some)[(order i).val]?.join =
      some (order (cyclicPartner mate h order i)).val := by
  simp only [List.getElem?_map, List.getElem?_eq_getElem (order i).isLt,
    Option.map_some, Option.join_some, cyclicPartner, Equiv.apply_symm_apply,
    rawPartner_val]

/-- The native stack scan commutes with an explicit port permutation. -/
theorem cyclicCheck_relabel {n : Nat} (mate : List Nat)
    (h : pairingValid mate = true) (order : Point n ≃ Fin mate.length)
    (xs stack : List (Point n)) :
    cyclicCheck (mate.map some) (xs.map fun i => (order i).val)
      (stack.map fun i => (order i).val) =
    cyclicCheck ((cyclicMate mate h order).map some) (xs.map Fin.val) (stack.map Fin.val) := by
  induction xs generalizing stack with
  | nil => cases stack <;> rfl
  | cons x xs ih =>
      cases stack with
      | nil =>
          simp only [List.map_cons, List.map_nil, cyclicCheck, orderedMate_lookup mate h order x,
            cyclicMate_lookup]
          exact ih [cyclicPartner mate h order x]
      | cons y ys =>
          by_cases he : x = y
          · subst y
            simp only [List.map_cons, cyclicCheck, beq_self_eq_true, ite_true]
            exact ih ys
          · have hxy : x.val ≠ y.val := fun hv => he (Fin.ext hv)
            have ho : (order x).val ≠ (order y).val :=
              fun hv => he (order.injective (Fin.ext hv))
            have hb : (x.val == y.val) = false := by simp [hxy]
            have hob : ((order x).val == (order y).val) = false := by simp [ho]
            simp only [List.map_cons, cyclicCheck, hb, hob, Bool.false_eq_true, ite_false,
              orderedMate_lookup mate h order x, cyclicMate_lookup]
            exact ih (cyclicPartner mate h order x :: y :: ys)

/-- The cyclic endpoint list attached to an explicit storage-order permutation. -/
def cyclicOrder {n : Nat} {mate : List Nat} (order : Point n ≃ Fin mate.length) : List Nat :=
  (List.finRange (2 * n)).map fun i => (order i).val

/-- The exact check on the storage-labelled cyclic list proves planarity of
its conjugated partner map. -/
theorem cyclicCheck_noncrossing {n : Nat} (mate : List Nat)
    (h : pairingValid mate = true) (order : Point n ≃ Fin mate.length)
    (hc : cyclicCheck (mate.map some) (cyclicOrder order) [] = true) :
    CyclicNoncrossing mate h order := by
  have hh := cyclicCheck_relabel mate h order (List.finRange (2 * n)) []
  simp only [List.map_nil] at hh
  rw [show (List.finRange (2 * n)).map Fin.val = List.range (2 * n) by simp] at hh
  rw [show (List.finRange (2 * n)).map (fun i => (order i).val) = cyclicOrder order
    from rfl] at hh
  rw [hh] at hc
  have hp := pairingValid_cyclicMate mate h order
  intro i j hij hji hfij
  have hi : i.val < (cyclicMate mate h order).length := by
    simpa only [length_cyclicMate] using i.isLt
  have hj : j.val < (cyclicMate mate h order).length := by
    simpa only [length_cyclicMate] using j.isLt
  have hlookup (a : Point n) : mateIndex (cyclicMate mate h order) a.val =
      (cyclicPartner mate h order a).val := by
    simp only [mateIndex, cyclicMate, List.getElem?_ofFn, dite_eq_left a.isLt, Option.getD_some]
  apply cyclicCheck_range_noncrossing hp (by simpa only [length_cyclicMate] using hc)
    hi hj hij
  · simpa only [hlookup, Fin.lt_def] using hji
  · simpa only [hlookup, Fin.lt_def] using hfij

private theorem cyclicCheck_matching_from {n : Nat} (m : NoncrossingMatching n)
    (mate : List Nat) (hlookup : ∀ i, i < 2 * n → mate[i]? = some (m.partnerIndex i))
    (d : Nat) : ∀ t, t + d = 2 * n →
    cyclicCheck (mate.map some) (List.range' t d)
      ((m.activeList t).map fun i => (m.partner i).val) = true := by
  induction d with
  | zero =>
      intro t ht
      have ha : m.activeList t = [] := by
        simp only [NoncrossingMatching.activeList,
          m.active_eq_empty (t := t) (by omega), Finset.sort_empty]
      simp only [List.range'_zero, ha, List.map_nil, cyclicCheck, List.isEmpty_nil]
  | succ d ih =>
      intro t ht
      let v : Point n := ⟨t, by omega⟩
      have hv : v.val = t := rfl
      have hm : (mate.map some)[t]?.join = some (m.partner v).val := by
        rw [List.getElem?_map, hlookup t (by omega)]
        simp only [Option.map_some, Option.join_some]
        rw [m.partnerIndex_eq (by omega)]
      have hn := ih (t + 1) (by omega)
      rw [List.range'_succ]
      by_cases hopen : m.opens v
      · have ha := m.activeList_succ_open hopen
        rw [hv] at ha
        rw [ha, List.map_cons] at hn
        cases hs : m.activeList t with
        | nil =>
            simp only [hs, List.map_nil] at hn ⊢
            simpa only [cyclicCheck, hm] using hn
        | cons w ws =>
            have hw : w ∈ m.active t := by
              rw [← m.mem_activeList]
              simp only [hs, List.mem_cons, true_or]
            have hpw : (m.partner w).val ≠ t := by
              intro he
              have hp : m.partner w = v := Fin.ext he
              have hew : w = m.partner v := by rw [← hp, m.partner_partner]
              have hwt := (m.mem_active.mp hw).1
              rw [hew] at hwt
              have hvo : t < (m.partner v).val := hopen
              omega
            have hb : (t == (m.partner w).val) = false := by simp [Ne.symm hpw]
            simp only [hs, List.map_cons] at hn ⊢
            simpa only [cyclicCheck, hb, Bool.false_eq_true, ite_false, hm] using hn
      · have ha := m.activeList_succ_close hopen
        rw [hv] at ha
        rw [ha, List.map_cons, m.partner_partner]
        change cyclicCheck (mate.map some) (t :: List.range' (t + 1) d)
          (t :: (m.activeList (t + 1)).map (fun i => (m.partner i).val)) = true
        simpa only [cyclicCheck, beq_self_eq_true, ite_true] using hn

/-- Every encoded noncrossing matching passes the actual stack checker. -/
theorem cyclicCheck_of_matching {n : Nat} (m : NoncrossingMatching n)
    (mate : List Nat) (hlookup : ∀ i, i < 2 * n → mate[i]? = some (m.partnerIndex i)) :
    cyclicCheck (mate.map some) (List.range (2 * n)) [] = true := by
  simpa only [← List.range_eq_range', m.activeList_zero, List.map_nil] using
    cyclicCheck_matching_from m mate hlookup (2 * n) 0 (by omega)

/-- The checker is both sound and complete for the explicit cyclic partner map. -/
theorem cyclicCheck_iff_noncrossing {n : Nat} (mate : List Nat)
    (h : pairingValid mate = true) (order : Point n ≃ Fin mate.length) :
    cyclicCheck (mate.map some) (cyclicOrder order) [] = true ↔
      CyclicNoncrossing mate h order := by
  constructor
  · exact cyclicCheck_noncrossing mate h order
  · intro hp
    have hscan := cyclicCheck_of_matching (matchingOfRaw mate h order hp)
      (cyclicMate mate h order) (by
        intro i hi
        rw [NoncrossingMatching.partnerIndex_eq _ hi, partner_matchingOfRaw]
        simp only [cyclicMate, List.getElem?_ofFn, dite_eq_left hi])
    have htransport := cyclicCheck_relabel mate h order (List.finRange (2 * n)) []
    simp only [List.map_nil] at htransport
    have hfin : (List.finRange (2 * n)).map Fin.val = List.range (2 * n) := by simp
    rw [hfin] at htransport
    exact htransport.trans hscan

/-- The cyclic order rearranges the same four groups, without dropping a port. -/
theorem Ports.cyclic_perm_flat (p : Ports) : p.cyclic.Perm p.flat := by
  unfold Ports.cyclic Ports.flat
  calc
    (p.pl.reverse ++ p.pr ++ p.qr.reverse ++ p.ql).Perm (p.pl ++ p.pr ++ p.qr ++ p.ql) :=
      (((List.reverse_perm p.pl).append (List.Perm.refl p.pr)).append
        (List.reverse_perm p.qr)).append (List.Perm.refl p.ql)
    (p.pl ++ p.pr ++ p.qr ++ p.ql).Perm (p.pl ++ p.pr ++ p.ql ++ p.qr) := by
      simpa only [List.append_assoc] using
        (List.Perm.refl (p.pl ++ p.pr)).append (List.perm_append_comm (l₁ := p.qr) (l₂ := p.ql))

/-- Consecutive storage groups enumerate their exact raw domain. -/
theorem Ports.flat_ofLengths (len : Counters) :
    (Ports.ofLengths len).flat = List.range (len.pl + len.pr + len.ql + len.qr) := by
  simp only [Ports.ofLengths, Ports.flat, ← List.range_add]

/-- In particular, the nonstandard cyclic group order is a genuine port permutation. -/
theorem Ports.cyclic_perm_range (len : Counters) :
    (Ports.ofLengths len).cyclic.Perm (List.range (len.pl + len.pr + len.ql + len.qr)) := by
  rw [← Ports.flat_ofLengths]
  exact Ports.cyclic_perm_flat _

/-- Reading a permutation list gives its exact finite port equivalence. -/
noncomputable def listPortEquiv {size : Nat} (xs : List Nat)
    (hp : xs.Perm (List.range size)) : Fin xs.length ≃ Fin size :=
  Equiv.ofBijective
    (fun i => ⟨xs.get i, List.mem_range.mp (hp.mem_iff.mp (xs.get_mem i))⟩) (by
      constructor
      · intro i j he
        exact (hp.nodup_iff.mpr List.nodup_range).get_inj_iff.mp (congrArg Fin.val he)
      · intro j
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp (hp.mem_iff.mpr (List.mem_range.mpr j.isLt))
        exact ⟨i, Fin.ext hi⟩)

@[simp] theorem listPortEquiv_val {size : Nat} (xs : List Nat)
    (hp : xs.Perm (List.range size)) (i : Fin xs.length) :
    (listPortEquiv xs hp i).val = xs.get i := rfl

/-- Rank-index the cyclic permutation without changing its listed endpoint labels. -/
noncomputable def orderFromList {n size : Nat} (xs : List Nat)
    (hp : xs.Perm (List.range size)) (hn : xs.length = 2 * n) : Point n ≃ Fin size :=
  (finCongr hn.symm).trans (listPortEquiv xs hp)

private theorem orderFromList_val {n size : Nat} (xs : List Nat)
    (hp : xs.Perm (List.range size)) (hn : xs.length = 2 * n) (i : Point n) :
    (orderFromList xs hp hn i).val = xs[i.val]'(by omega) := rfl

/-- The extracted equivalence enumerates precisely the supplied cyclic list. -/
theorem cyclicOrder_orderFromList {n : Nat} {mate : List Nat} (xs : List Nat)
    (hp : xs.Perm (List.range mate.length)) (hn : xs.length = 2 * n) :
    cyclicOrder (orderFromList xs hp hn) = xs := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 2 * n
  · have hib : i < xs.length := by omega
    simp [cyclicOrder, hi, hib, orderFromList_val]
  · have hib : xs.length ≤ i := by omega
    rw [List.getElem?_eq_none (by
      simp only [cyclicOrder, List.length_map, List.length_finRange]
      omega), List.getElem?_eq_none hib]

/-- Concrete cyclic permutation reconstructed from the four native group lengths. -/
noncomputable def portsOrder {n : Nat} (mate : List Nat) (len : Counters)
    (hlen : mate.length = (Ports.ofLengths len).flat.length) (hn : mate.length = 2 * n) :
    Point n ≃ Fin mate.length :=
  orderFromList (Ports.ofLengths len).cyclic (by
    have hp := Ports.cyclic_perm_range len
    have hl : mate.length = len.pl + len.pr + len.ql + len.qr := by
      simpa only [Ports.flat_ofLengths, List.length_range] using hlen
    simpa only [hl] using hp) (by
      have hp := (Ports.cyclic_perm_flat (Ports.ofLengths len)).length_eq
      omega)

/-- Native cyclic order and semantic cyclic order have identical endpoint lists. -/
theorem cyclicOrder_portsOrder {n : Nat} (mate : List Nat) (len : Counters)
    (hlen : mate.length = (Ports.ofLengths len).flat.length) (hn : mate.length = 2 * n) :
    cyclicOrder (portsOrder mate len hlen hn) = (Ports.ofLengths len).cyclic :=
  cyclicOrder_orderFromList _ _ _

/-- Extract the native array contract without treating any check as a proof of planarity. -/
theorem validKey_pairing_contract {s : RunSpec} {t : Stage} {x : Key}
    (h : validKey s t x = true) :
    x.mate.length = (Ports.ofLengths (geometry s t x.counters).length).flat.length ∧
    pairingValid x.mate = true ∧
    cyclicCheck (x.mate.map some) (Ports.ofLengths (geometry s t x.counters).length).cyclic [] =
      true := by
  simp only [validKey, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.2.1, h.1.2, h.2⟩

/-- The validated key has exactly twice its derived pairing rank many endpoints. -/
theorem validKey_twice_rank {s : RunSpec} {t : Stage} {x : Key}
    (h : validKey s t x = true) : x.mate.length = 2 * (x.mate.length / 2) := by
  obtain ⟨k, hk⟩ := pairingValid_even_length (validKey_pairing_contract h).2.1
  omega

/-- The native four-group cyclic ordering as an actual permutation of raw names. -/
noncomputable def keyOrder (s : RunSpec) (t : Stage) (x : Key) (h : validKey s t x = true) :
    Point (x.mate.length / 2) ≃ Fin x.mate.length :=
  portsOrder x.mate (geometry s t x.counters).length (validKey_pairing_contract h).1
    (validKey_twice_rank h)

/-- Decode a validated key to the canonical noncrossing matching on its actual
cyclic boundary. Soundness comes from the proved stack-check characterization. -/
noncomputable def decodeKey (s : RunSpec) (t : Stage) (x : Key) (h : validKey s t x = true) :
    NoncrossingMatching (x.mate.length / 2) :=
  matchingOfRaw x.mate (validKey_pairing_contract h).2.1 (keyOrder s t x h)
    (cyclicCheck_noncrossing _ _ _ (by
      rw [show cyclicOrder (keyOrder s t x h) =
          (Ports.ofLengths (geometry s t x.counters).length).cyclic from
        cyclicOrder_portsOrder _ _ _ _]
      exact (validKey_pairing_contract h).2.2))

/-- Re-encoding the decoded geometric pairing recovers the exact raw mate list. -/
theorem decodeKey_roundtrip (s : RunSpec) (t : Stage) (x : Key)
    (h : validKey s t x = true) :
    encodeMatching (decodeKey s t x h) (keyOrder s t x h) = x.mate :=
  encodeMatching_matchingOfRaw _ _ _ _

/-- Decoding retains the mate of every individual original storage endpoint. -/
theorem decodeKey_storage_partner (s : RunSpec) (t : Stage) (x : Key)
    (h : validKey s t x = true) (i : Fin x.mate.length) :
    keyOrder s t x h ((decodeKey s t x h).partner ((keyOrder s t x h).symm i)) =
      rawPartner x.mate (validKey_pairing_contract h).2.1 i :=
  matchingOfRaw_storage_partner _ _ _ _ _

end Meanders.FirstCrossing
