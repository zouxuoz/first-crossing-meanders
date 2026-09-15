import Meanders.Models.FirstCrossing.Packed.Transition

/-!
# Exact labelled and finite-word refinement

List equality preserves all four labelled contributions, including collisions.
The finite-word adapter is proved lossless under the sector's explicit port
bound; no fixed-width truncation is accepted as mathematical pruning.
-/

namespace Meanders.FirstCrossing.Packed

/-- Validated native states fit every capacity at least the fixed sector port bound. -/
theorem fits_of_validKey {width : Nat} {s : RunSpec} {t : Stage} {x : FirstCrossing.Key}
    (hx : validKey s t x = true) (hw : s.portBound ≤ width) : Fits width s t x.counters := by
  have hbound : x.mate.length ≤ s.portBound := by
    simp only [validKey, Bool.and_eq_true, decide_eq_true_eq] at hx
    exact hx.1.1.2.2.1
  have hlength : (names s t x.counters).length = x.mate.length := by
    rw [← orderNames_keyOrder s t x hx, orderNames_length, ← validKey_twice_rank hx]
  unfold Fits
  rw [hlength]
  exact hbound.trans hw

/-- Every successful packed successor fits a sector-wide finite word capacity. -/
theorem step_output_bound {width : Nat} {s : RunSpec} {t : Stage} {k out : Key}
    {m : Move} {increment : Nat} (hw : s.portBound ≤ width)
    (h : step s t k m = some (out, increment)) : out.bits < 2 ^ width := by
  unfold step rawStep at h
  cases hs : s.schedule[t.tick]? with
  | none => simp [hs] at h
  | some side =>
    simp only [hs] at h
    cases hr : FirstCrossing.rawStep s t (decode s t k) m with
    | none => simp [hr] at h
    | some native =>
      have he : (encode s (t.next side) native, lowerIncrement t (decode s t k) m side) =
          (out, increment) := by simpa [hr] using h
      obtain ⟨side', hs', hv⟩ := rawStep_valid hr
      have hside : side' = side := Option.some.inj (hs'.symm.trans hs)
      subst side'
      rw [← (Prod.mk.inj he).1]
      exact encode_lt_word native (fits_of_validKey hv hw)

/-- The actual finite-width payload, with the original counters stored separately. -/
structure WordKey (width : Nat) where
  /-- Original uncontracted down counts. -/
  counters : Counters
  /-- Exactly `width` bits, represented by Lean's concrete bitvector type. -/
  bits : BitVec width
  deriving DecidableEq, Repr

/-- Machine storage writes the payload into its finite bitvector. -/
def toWord (width : Nat) (k : Key) : WordKey width := ⟨k.counters, BitVec.ofNat width k.bits⟩

/-- Reading finite storage recovers its exact unsigned payload. -/
def ofWord {width : Nat} (k : WordKey width) : Key := ⟨k.counters, k.bits.toNat⟩

/-- The explicit bound makes machine storage exact, rather than truncating. -/
theorem ofWord_toWord {width : Nat} (k : Key) (hb : k.bits < 2 ^ width) :
    ofWord (toWord width k) = k := by
  simp only [ofWord, toWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

/-- A finite-word step uses the same labelled recurrence and original increment. -/
def wordStep {width : Nat} (s : RunSpec) (t : Stage) (k : WordKey width) (m : Move) :
    Option (WordKey width × Nat) :=
  (step s t (ofWord k) m).map fun edge => (toWord width edge.1, edge.2)

/-- Under the fixed sector bound, reading a machine successor loses no output bit. -/
theorem ofWord_wordStep {width : Nat} {s : RunSpec} {t : Stage}
    (k : WordKey width) (hw : s.portBound ≤ width) (m : Move) :
    (wordStep s t k m).map (fun edge => (ofWord edge.1, edge.2)) =
      step s t (ofWord k) m := by
  unfold wordStep
  cases he : step s t (ofWord k) m with
  | none => rfl
  | some edge =>
    have hb := step_output_bound hw he
    simp only [Option.map_some, ofWord_toWord edge.1 hb]

/-- Finite machine words decode to the exact native labelled edge, with rejection
and increments unchanged. Width 64 is the production u64 specialization. -/
theorem decode_wordStep {width : Nat} {s : RunSpec} {t : Stage}
    (k : WordKey width) (hw : s.portBound ≤ width) {side : Side}
    (hs : s.schedule[t.tick]? = some side) (m : Move) :
    (wordStep s t k m).map (fun edge => (decode s (t.next side) (ofWord edge.1), edge.2)) =
      FirstCrossing.step s t (decode s t (ofWord k)) m := by
  have he := congrArg
    (Option.map fun edge : Key × Nat => (decode s (t.next side) edge.1, edge.2))
    (ofWord_wordStep (t := t) k hw m)
  simpa only [Option.map_map, Function.comp_def, decode_step _ hs m] using he

/-- A validated source key survives finite storage without any counter or mate change. -/
theorem decode_wordEncode {width : Nat} {s : RunSpec} {t : Stage} (x : FirstCrossing.Key)
    (hx : validKey s t x = true) (hw : s.portBound ≤ width) :
    decode s t (ofWord (toWord width (encode s t x))) = x := by
  rw [ofWord_toWord _ (encode_lt_word x (fits_of_validKey hx hw)), decode_encode s t x hx]

/-- Finite storage cannot merge distinct validated native keys under the sector bound. -/
theorem wordEncode_injective {width : Nat} {s : RunSpec} {t : Stage}
    {x y : FirstCrossing.Key} (hx : validKey s t x = true) (hy : validKey s t y = true)
    (hw : s.portBound ≤ width)
    (he : toWord width (encode s t x) = toWord width (encode s t y)) : x = y := by
  have h := congrArg (fun k => decode s t (ofWord k)) he
  simpa only [decode_wordEncode x hx hw, decode_wordEncode y hy hw] using h

/-- Machine successors retain each of the four labelled contributions. -/
def wordSuccessors {width : Nat} (s : RunSpec) (t : Stage) (k : WordKey width) :
    List (WordKey width × Nat) := Move.all.filterMap (wordStep s t k)

/-- Exact decoded successor-list equality includes multiplicities, increments,
rejections, and all native terminal-cycle decisions. -/
theorem decode_wordSuccessors {width : Nat} {s : RunSpec} {t : Stage}
    (k : WordKey width) (hw : s.portBound ≤ width) {side : Side}
    (hs : s.schedule[t.tick]? = some side) :
    (wordSuccessors s t k).map
      (fun edge => (decode s (t.next side) (ofWord edge.1), edge.2)) =
      Move.all.filterMap (FirstCrossing.step s t (decode s t (ofWord k))) := by
  simp only [wordSuccessors, List.map_filterMap]
  congr 1
  funext m
  exact decode_wordStep k hw hs m

/-- A completed or out-of-schedule layer has no machine successors. -/
theorem wordSuccessors_none_of_schedule_none {width : Nat} {s : RunSpec} {t : Stage}
    (k : WordKey width) (hs : s.schedule[t.tick]? = none) : wordSuccessors s t k = [] := by
  simp [wordSuccessors, wordStep, step_none_of_schedule_none _ hs]

end Meanders.FirstCrossing.Packed
