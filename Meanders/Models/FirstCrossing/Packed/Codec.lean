import Meanders.Models.FirstCrossing.Packed.State

/-!
# Exact cyclic bit codec for native keys

Encoding reads the native cyclic ordering. Decoding scans the recovered Dyck
word and restores the original storage indices. Both operations are concrete;
the existing native codec supplies their noncrossing-matching interpretation.
-/

namespace Meanders.FirstCrossing.Packed

/-- Geometry determines the exact storage names in cyclic bit order. -/
def names (s : RunSpec) (t : Stage) (c : Counters) : List Nat :=
  (Ports.ofLengths (geometry s t c).length).cyclic

/-- The raw key's mate array becomes its cyclic opener-bit payload. -/
def encode (s : RunSpec) (t : Stage) (x : FirstCrossing.Key) : Key :=
  ⟨x.counters, packBits (cyclicWord x.mate (names s t x.counters))⟩

/-- The fixed group lengths recover the payload length and restore stored mates. -/
def decode (s : RunSpec) (t : Stage) (k : Key) : FirstCrossing.Key :=
  let order := names s t k.counters
  ⟨k.counters, storageMate (unpackBits order.length k.bits) order⟩

/-- The codec's explicit list agrees with the previously verified port permutation. -/
theorem orderNames_keyOrder (s : RunSpec) (t : Stage) (x : FirstCrossing.Key)
    (hx : validKey s t x = true) :
    orderNames (keyOrder s t x hx) = names s t x.counters := by
  change orderNames (keyOrder s t x hx) = (Ports.ofLengths _).cyclic
  rw [show orderNames (keyOrder s t x hx) = cyclicOrder (keyOrder s t x hx) by
    simp only [orderNames, List.ofFn_eq_map, cyclicOrder]]
  exact cyclicOrder_portsOrder _ _ _ _

/-- A validated native pairing produces exactly its cyclic matching's Dyck word. -/
theorem cyclicWord_valid (s : RunSpec) (t : Stage) (x : FirstCrossing.Key)
    (hx : validKey s t x = true) :
    cyclicWord x.mate (names s t x.counters) = (decodeKey s t x hx).wordOf := by
  calc
    cyclicWord x.mate (names s t x.counters) =
        cyclicWord (encodeMatching (decodeKey s t x hx) (keyOrder s t x hx))
          (orderNames (keyOrder s t x hx)) :=
      congrArg₂ cyclicWord (decodeKey_roundtrip s t x hx).symm
        (orderNames_keyOrder s t x hx).symm
    _ = _ := cyclicWord_encodeMatching _ _

/-- Decoding restores every original counter and every mate entry exactly. -/
theorem decode_encode (s : RunSpec) (t : Stage) (x : FirstCrossing.Key)
    (hx : validKey s t x = true) : decode s t (encode s t x) = x := by
  have hlength : (cyclicWord x.mate (names s t x.counters)).length =
      (names s t x.counters).length := by simp [cyclicWord]
  unfold decode encode
  dsimp only
  rw [← hlength, unpackBits_packBits, cyclicWord_valid s t x hx,
    ← orderNames_keyOrder s t x hx, storageMate_wordOf, decodeKey_roundtrip]

/-- Every payload bit is exactly the original opener at that cyclic position. -/
theorem packBits_testBit (w : List DyckStep) {i : Nat} (hi : i < w.length) :
    (packBits w).testBit i = (w[i]? == some DyckStep.U) := by
  have h := Nat.testBit_two_pow_add_gt hi (packBits w)
  rw [packBits, Nat.add_sub_of_le (two_pow_length_le_pack w)] at h
  rw [packBits, ← h, testBit_pack]
  simp only [beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hi), Bool.or_false]

/-- The native finite-word capacity condition contains only geometric length. -/
def Fits (width : Nat) (s : RunSpec) (t : Stage) (c : Counters) : Prop :=
  (names s t c).length ≤ width

/-- Under the explicit capacity condition the encoded payload fits the chosen word. -/
theorem encode_lt_word {width : Nat} {s : RunSpec} {t : Stage} (x : FirstCrossing.Key)
    (hfit : Fits width s t x.counters) : (encode s t x).bits < 2 ^ width := by
  apply packBits_lt_word
  simpa only [Fits, cyclicWord, List.length_map] using hfit

/-- Geometry lists every storage name exactly once, regardless of payload validity. -/
theorem names_perm (s : RunSpec) (t : Stage) (c : Counters) :
    (names s t c).Perm (List.range (names s t c).length) := by
  have hp := Ports.cyclic_perm_range (geometry s t c).length
  have hl := hp.length_eq
  simp only [List.length_range] at hl
  simpa only [names, hl] using hp

/-- Packed well-formedness is the independently decoded Dyck condition and the
exact finite payload range; it assumes no native successor or source existence. -/
def WellFormed (s : RunSpec) (t : Stage) (k : Key) : Prop :=
  k.bits < 2 ^ (names s t k.counters).length ∧
    IsDyck ((names s t k.counters).length / 2)
      (unpackBits (names s t k.counters).length k.bits)

/-- Decoding and re-encoding preserves every well-formed packed payload exactly. -/
theorem encode_decode {s : RunSpec} {t : Stage} {k : Key}
    (hk : WellFormed s t k) : encode s t (decode s t k) = k := by
  obtain ⟨hb, hdyck⟩ := hk
  let ns := names s t k.counters
  have hl : ns.length = 2 * (ns.length / 2) :=
    (length_unpackBits hb).symm.trans hdyck.length
  let order : Point (ns.length / 2) ≃ Fin ns.length :=
    orderFromList ns (names_perm s t k.counters) hl
  have ho : orderNames order = ns := by
    have hh := cyclicOrder_orderFromList (mate := ns) ns (names_perm s t k.counters) hl
    simpa only [order, orderNames, List.ofFn_eq_map, cyclicOrder] using hh
  let matching := ofDyck hdyck
  have hw : matching.wordOf = unpackBits ns.length k.bits := wordOf_ofDyck hdyck
  have hword : cyclicWord (storageMate (unpackBits ns.length k.bits) ns) ns =
      unpackBits ns.length k.bits := by
    calc
      cyclicWord (storageMate (unpackBits ns.length k.bits) ns) ns =
          cyclicWord (storageMate matching.wordOf (orderNames order)) (orderNames order) := by
        rw [ho, hw]
      _ = matching.wordOf := by rw [storageMate_wordOf, cyclicWord_encodeMatching]
      _ = _ := hw
  change (⟨k.counters, packBits (cyclicWord
    (storageMate (unpackBits ns.length k.bits) ns) ns)⟩ : Key) = k
  rw [hword, packBits_unpackBits hb]

/-- Bit `i` tests whether the stored partner lies later in the fixed cyclic order.
This is the direct finite-word encoder used by the production implementation. -/
theorem encode_bit (s : RunSpec) (t : Stage) (x : FirstCrossing.Key) {i : Nat}
    (hi : i < (names s t x.counters).length) :
    (encode s t x).bits.testBit i = decide
      (i < (names s t x.counters).idxOf
        (mateIndex x.mate ((names s t x.counters)[i]))) := by
  have hn := (names_perm s t x.counters).nodup_iff.mpr List.nodup_range
  have hidx := hn.idxOf_getElem i hi
  change (packBits (cyclicWord x.mate (names s t x.counters))).testBit i = _
  rw [packBits_testBit _ (by simpa only [cyclicWord, List.length_map] using hi),
    cyclicWord, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some, hidx]
  split <;> simp_all [show (DyckStep.D == DyckStep.U) = false from rfl]

end Meanders.FirstCrossing.Packed
