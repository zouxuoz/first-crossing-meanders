import Meanders.Models.FirstCrossing.Native.Codec
import Meanders.Core.Word.Bits
import Meanders.Core.Matching.WordPartner

/-!
# Packed First-Crossing pairing storage

Original counters remain unchanged. Bit `i` records an opener in the exact
native cyclic order, without a sentinel: geometry supplies the word length.
The mathematical natural payload models a machine word only under the explicit
capacity bound. No owner reflection or state quotient is introduced.
-/

namespace Meanders.FirstCrossing.Packed

open DyckStep

/-- The original four counters and the finite pairing bit payload. -/
structure Key where
  /-- Original down counts, never contracted or packed into observer bits. -/
  counters : Counters
  /-- Opener bits in `rev(PL), PR, rev(QR), QL` order, least significant first. -/
  bits : Nat
  deriving DecidableEq, Repr

/-- Remove the existing word codec's sentinel; length remains external metadata. -/
def packBits (w : List DyckStep) : Nat := pack w - 2 ^ w.length

/-- Restore the sentinel at the prescribed length before reusing the word decoder. -/
def unpackBits (length bits : Nat) : List DyckStep := unpack (2 ^ length + bits)

/-- Stripping and restoring the sentinel loses no original letter. -/
theorem unpackBits_packBits (w : List DyckStep) : unpackBits w.length (packBits w) = w := by
  rw [unpackBits, packBits, Nat.add_sub_of_le (two_pow_length_le_pack w), unpack_pack]

/-- The payload fits exactly in the original word length, including the empty word. -/
theorem packBits_lt (w : List DyckStep) : packBits w < 2 ^ w.length := by
  have h := pack_lt w
  have hl := two_pow_length_le_pack w
  rw [pow_succ] at h
  unfold packBits
  omega

/-- An explicit capacity bound is sufficient for an exact finite machine word. -/
theorem packBits_lt_word {w : List DyckStep} {width : Nat} (hw : w.length ≤ width) :
    packBits w < 2 ^ width :=
  (packBits_lt w).trans_le (Nat.pow_le_pow_right (by decide) hw)

/-- Fixed-length decoding retains exactly the supplied length for an in-range payload. -/
theorem length_unpackBits {length bits : Nat} (hb : bits < 2 ^ length) :
    (unpackBits length bits).length = length := by
  rw [unpackBits, length_unpack, Nat.log2_eq_iff (by positivity)]
  constructor
  · omega
  · rw [pow_succ]
    omega

/-- No unused high bits or alternate encodings survive the finite payload contract. -/
theorem packBits_unpackBits {length bits : Nat} (hb : bits < 2 ^ length) :
    packBits (unpackBits length bits) = bits := by
  rw [packBits, length_unpackBits hb, unpackBits, pack_unpack (by positivity)]
  omega

/-- Read either endpoint's mate by the existing original-word partner scans. -/
def wordPartner (w : List DyckStep) (i : Nat) : Nat :=
  if w[i]? = some U then (partnerOf w i).getD i else (leftPartnerOf w i).getD i

/-- The two concrete scans recover the matching partner at either endpoint. -/
theorem wordPartner_wordOf {n : Nat} (m : NoncrossingMatching n) {i : Nat}
    (hi : i < 2 * n) : wordPartner m.wordOf i = m.partnerIndex i := by
  rw [wordPartner, m.getElem?_wordOf hi]
  by_cases h : i < m.partnerIndex i
  · simp only [h, ite_true]
    rw [NoncrossingMatching.partnerOf_wordOf m hi h]
    rfl
  · have hne : i ≠ m.partnerIndex i := by
      intro he
      apply m.partner_ne ⟨i, hi⟩
      exact Fin.ext (by simpa only [m.partnerIndex_eq hi] using he.symm)
    have hl : m.partnerIndex i < i := by omega
    simp only [h, ite_false]
    rw [NoncrossingMatching.leftPartnerOf_wordOf m hi hl]
    rfl

/-- The exact concrete names of a cyclic port equivalence. -/
def orderNames {n size : Nat} (order : Point n ≃ Fin size) : List Nat :=
  List.ofFn fun i => (order i).val

@[simp] theorem orderNames_length {n size : Nat} (order : Point n ≃ Fin size) :
    (orderNames order).length = 2 * n := by simp [orderNames]

/-- Looking up a cyclic slot gives its original storage name. -/
theorem orderNames_lookup {n size : Nat} (order : Point n ≃ Fin size) (i : Point n) :
    (orderNames order)[i.val]? = some (order i).val := by
  simp [orderNames, i.isLt]

/-- A port equivalence lists every name at a unique cyclic position. -/
theorem orderNames_nodup {n size : Nat} (order : Point n ≃ Fin size) :
    (orderNames order).Nodup := by
  rw [orderNames, List.nodup_ofFn]
  intro i j he
  exact order.injective (Fin.ext he)

/-- Storage-to-cyclic lookup is exactly the inverse of the explicit port equivalence. -/
theorem orderNames_idxOf {n size : Nat} (order : Point n ≃ Fin size) (i : Point n) :
    (orderNames order).idxOf (order i).val = i.val := by
  have hi : i.val < (orderNames order).length := by
    rw [orderNames_length]
    exact i.isLt
  have he : (orderNames order)[i.val] = (order i).val := by
    simpa only [List.getElem?_eq_getElem hi, Option.some.injEq] using orderNames_lookup order i
  rw [← he]
  exact (orderNames_nodup order).idxOf_getElem i.val hi

/-- Encode one opener bit for each cyclic endpoint of the raw stored mate list. -/
def cyclicWord (mate order : List Nat) : List DyckStep :=
  order.map fun i => if order.idxOf i < order.idxOf (mateIndex mate i) then U else D

/-- Decode a cyclic word by the actual partner scan and relabel to storage positions. -/
def storageMate (word : List DyckStep) (order : List Nat) : List Nat :=
  (List.range order.length).map fun i => (order[wordPartner word (order.idxOf i)]?).getD i

/-- The cyclic opener test exactly recovers the decoded matching word. -/
theorem cyclicWord_encodeMatching {n size : Nat} (m : NoncrossingMatching n)
    (order : Point n ≃ Fin size) :
    cyclicWord (encodeMatching m order) (orderNames order) = m.wordOf := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 2 * n
  · let v : Point n := ⟨i, hi⟩
    have hm : mateIndex (encodeMatching m order) (order v).val =
        (order (m.partner v)).val := by
      rw [mateIndex, getElem?_encodeMatching m order (order v).isLt]
      change (order (m.partner (order.symm (order v)))).val = _
      rw [Equiv.symm_apply_apply]
    rw [cyclicWord, List.getElem?_map, orderNames_lookup order v, Option.map_some,
      orderNames_idxOf, hm, orderNames_idxOf, m.getElem?_wordOf hi, m.partnerIndex_eq hi]
  · rw [List.getElem?_eq_none (by simp [cyclicWord]; omega),
      List.getElem?_eq_none (by simp; omega)]

/-- Concrete word scanning and inverse port permutation recover every stored mate. -/
theorem storageMate_wordOf {n size : Nat} (m : NoncrossingMatching n)
    (order : Point n ≃ Fin size) :
    storageMate m.wordOf (orderNames order) = encodeMatching m order := by
  have hsize : 2 * n = size := by simpa using Fintype.card_congr order
  apply List.ext_getElem?
  intro i
  by_cases hi : i < size
  · let v : Point n := order.symm ⟨i, hi⟩
    have ho : (order v).val = i := by simp [v]
    have hidx : (orderNames order).idxOf i = v.val := by
      rw [← ho, orderNames_idxOf]
    have hbound : i < (orderNames order).length := by simpa [hsize] using hi
    rw [storageMate, List.getElem?_map, List.getElem?_range hbound, Option.map_some,
      hidx, wordPartner_wordOf m v.isLt, m.partnerIndex_eq v.isLt,
      orderNames_lookup order (m.partner v), Option.getD_some,
      getElem?_encodeMatching m order hi]
  · rw [List.getElem?_eq_none (by simp [storageMate, hsize]; omega),
      List.getElem?_eq_none (by simp; omega)]

end Meanders.FirstCrossing.Packed
