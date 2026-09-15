import Meanders.Models.FirstCrossing.Correctness.ClosedBridge

/-!
# The native key determines all accepted continuations

Completions are actual accepted full words extending a successful prefix.
Replacing that prefix preserves every suffix label and its future lower event
increment. Past increments remain external weights and may differ.
-/

namespace Meanders.FirstCrossing

/-- The actual deterministic interpreter composes prefixes and suffixes while
adding their lower-event increments externally to the state. -/
theorem followLabels_append (spec : RunSpec) (tick : Nat) (key : Key)
    (pre suffix : List Move) :
    FirstCrossing.followLabels spec (Stage.ofTick spec tick) key (pre ++ suffix) = do
      let (middle, past) ← FirstCrossing.followLabels spec (Stage.ofTick spec tick) key pre
      let (last, future) ← FirstCrossing.followLabels spec
        (Stage.ofTick spec (tick + pre.length)) middle suffix
      return (last, past + future) := by
  induction pre generalizing tick key with
  | nil => simp [followLabels]
  | cons m ms ih =>
    cases hs : spec.schedule[tick]? with
    | none => simp [followLabels, hs, Stage.ofTick]
    | some side =>
      cases he : step spec (Stage.ofTick spec tick) key m with
      | none => simp [followLabels, he]
      | some pair =>
        rcases pair with ⟨middle, past⟩
        have hstage := Stage.ofTick_next spec tick hs
        have hi := ih (tick + 1) middle
        rw [hstage] at hi
        simp only [List.cons_append, followLabels,
          show (Stage.ofTick spec tick).tick = tick from rfl,
          hs, Option.bind_eq_bind, Option.bind_some, he] at ⊢
        rw [hi]
        have hsum : tick + (m :: ms).length = tick + 1 + ms.length := by simp; omega
        rw [hsum]
        cases hp : FirstCrossing.followLabels spec
            ((Stage.ofTick spec tick).next side) middle ms with
        | none => simp
        | some pair =>
          rcases pair with ⟨last, increment⟩
          cases hf : FirstCrossing.followLabels spec
              (Stage.ofTick spec (tick + 1 + ms.length)) last suffix with
          | none => simp [hf, Option.bind_eq_bind]
          | some pair =>
            rcases pair with ⟨out, final⟩
            simp only [Nat.add_assoc] at hf
            simp [hf, Option.bind_eq_bind, Nat.add_assoc]

/-- A successful prefix exposes exactly the remaining interpreter run and the
affine relation between old, future, and full lower increments. -/
theorem followLabels_append_iff {spec : RunSpec} {pre suffix : List Move}
    {key last : Key} {past total : Nat}
    (hp : FirstCrossing.followLabels spec ⟨0, 0, 0⟩ Key.empty pre = some (key, past)) :
    FirstCrossing.followLabels spec ⟨0, 0, 0⟩ Key.empty (pre ++ suffix) = some (last, total) ↔
      ∃ future, FirstCrossing.followLabels spec (Stage.ofTick spec pre.length) key suffix =
        some (last, future) ∧ total = past + future := by
  have he := followLabels_append spec 0 Key.empty pre suffix
  simp only [show Stage.ofTick spec 0 = ⟨0, 0, 0⟩ from rfl, hp, Nat.zero_add,
    Option.bind_eq_bind, Option.bind_some] at he
  rw [he]
  cases hf : FirstCrossing.followLabels spec (Stage.ofTick spec pre.length) key suffix with
  | none => simp
  | some pair =>
    rcases pair with ⟨out, future⟩
    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq]
    aesop

/-- The labels of a successful prefix have exactly its actual native tick length. -/
theorem NativeHistory.labels_length {spec : RunSpec} {t : Stage} {key : Key}
    {events : List (Side × Move)} (h : NativeHistory spec t key events) :
    (events.map Prod.snd).length = t.tick := by
  induction h with
  | nil => rfl
  | @snoc t x events side m y h hs hraw ih =>
    cases side <;> simp only [List.length_map, List.length_append, List.length_singleton,
      Stage.next] at ih ⊢ <;> omega

/-- Actual accepted full label words which extend a prescribed original prefix. -/
abbrev PrefixCompletion (spec : RunSpec) (pre : List Move) :=
  {word : AcceptedWord spec // pre.IsPrefix word.val}

/-- Every successful native prefix is interpreted by its exact labels, with its
actual past lower increment kept separate from the raw key. -/
theorem NativeHistory.followLabels {spec : RunSpec} {t : Stage} {key : Key}
    {events : List (Side × Move)} (h : NativeHistory spec t key events)
    (hv : spec.valid = true) :
    ∃ past, FirstCrossing.followLabels spec ⟨0, 0, 0⟩ Key.empty (events.map Prod.snd) =
      some (key, past) := by
  induction h with
  | nil => exact ⟨0, rfl⟩
  | @snoc t x events side m y h hs hraw ih =>
    obtain ⟨past, hp⟩ := ih
    have hstage : Stage.ofTick spec (events.map Prod.snd).length = t := by
      rw [h.labels_length]
      exact (of_decide_eq_true (h.stage_valid hv)).2.symm
    refine ⟨past + lowerIncrement t x m side, ?_⟩
    rw [List.map_append, List.map_singleton]
    apply (followLabels_append_iff hp).mpr
    refine ⟨lowerIncrement t x m side, ?_, rfl⟩
    rw [hstage]
    simpa only [Nat.add_zero] using followLabels_cons_of_raw hs hraw
      (show FirstCrossing.followLabels spec (t.next side) y [] = some (y, 0) from rfl)

/-- The exact past event total of a successful prefix, external to its native key. -/
noncomputable def NativeHistory.past {spec : RunSpec} {t : Stage} {key : Key}
    {events : List (Side × Move)} (h : NativeHistory spec t key events)
    (hv : spec.valid = true) : Nat := Classical.choose (h.followLabels hv)

theorem NativeHistory.followLabels_past {spec : RunSpec} {t : Stage} {key : Key}
    {events : List (Side × Move)} (h : NativeHistory spec t key events)
    (hv : spec.valid = true) :
    FirstCrossing.followLabels spec ⟨0, 0, 0⟩ Key.empty (events.map Prod.snd) =
      some (key, h.past hv) :=
  Classical.choose_spec (h.followLabels hv)

private theorem replacePrefix_mem {spec : RunSpec} {pre other : List Move}
    {key : Key} {past otherPast : Nat} (hlen : pre.length = other.length)
    (hp : FirstCrossing.followLabels spec ⟨0, 0, 0⟩ Key.empty pre = some (key, past))
    (ho : FirstCrossing.followLabels spec ⟨0, 0, 0⟩ Key.empty other = some (key, otherPast))
    (word : PrefixCompletion spec pre) :
    other ++ word.val.val.drop pre.length ∈ acceptedWords spec := by
  obtain ⟨last, total, hfull, hterminal⟩ := word.val.accepted
  have hsplit := List.prefix_iff_eq_append.mp word.property
  rw [← hsplit] at hfull
  obtain ⟨future, hfuture, _⟩ := (followLabels_append_iff hp).mp hfull
  have hnew : FirstCrossing.followLabels spec ⟨0, 0, 0⟩ Key.empty
      (other ++ word.val.val.drop pre.length) = some (last, otherPast + future) := by
    apply (followLabels_append_iff ho).mpr
    exact ⟨future, by simpa only [hlen] using hfuture, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨List.mem_toFinset.mpr (mem_labelWords.mpr ?_), ?_⟩
  · have hl := word.val.length
    have hb := word.property.length_le
    simp only [List.length_append, List.length_drop]
    omega
  · simp only [hnew, Option.any_some, hterminal]

/-- Replace an actual accepted full word's successful prefix, keeping its
complete suffix literally unchanged. -/
def replacePrefixCompletion {spec : RunSpec} {pre other : List Move}
    {key : Key} {past otherPast : Nat} (hlen : pre.length = other.length)
    (hp : FirstCrossing.followLabels spec ⟨0, 0, 0⟩ Key.empty pre = some (key, past))
    (ho : FirstCrossing.followLabels spec ⟨0, 0, 0⟩ Key.empty other = some (key, otherPast))
    (word : PrefixCompletion spec pre) : PrefixCompletion spec other :=
  ⟨⟨other ++ word.val.val.drop pre.length, replacePrefix_mem hlen hp ho word⟩,
    List.prefix_append _ _⟩

private theorem replacePrefix_inverse {spec : RunSpec} {pre other : List Move}
    {key : Key} {past otherPast : Nat} (hlen : pre.length = other.length)
    (hp : FirstCrossing.followLabels spec ⟨0, 0, 0⟩ Key.empty pre = some (key, past))
    (ho : FirstCrossing.followLabels spec ⟨0, 0, 0⟩ Key.empty other = some (key, otherPast))
    (word : PrefixCompletion spec pre) :
    replacePrefixCompletion hlen.symm ho hp (replacePrefixCompletion hlen hp ho word) = word := by
  apply Subtype.ext
  apply Subtype.ext
  change pre ++ (other ++ word.val.val.drop pre.length).drop other.length = word.val.val
  rw [List.drop_left]
  exact List.prefix_iff_eq_append.mp word.property

/-- Two actual successful native prefixes ending at the same stage and raw key
have equivalent accepted full-word extensions, by literal suffix-preserving
prefix replacement. Historical lower totals are not part of the key. -/
noncomputable def stateFutureEquiv {spec : RunSpec} {t : Stage} {key : Key}
    {events otherEvents : List (Side × Move)} (hv : spec.valid = true)
    (h : NativeHistory spec t key events) (other : NativeHistory spec t key otherEvents) :
    PrefixCompletion spec (events.map Prod.snd) ≃
      PrefixCompletion spec (otherEvents.map Prod.snd) where
  toFun := replacePrefixCompletion (h.labels_length.trans other.labels_length.symm)
    (h.followLabels_past hv) (other.followLabels_past hv)
  invFun := replacePrefixCompletion (other.labels_length.trans h.labels_length.symm)
    (other.followLabels_past hv) (h.followLabels_past hv)
  left_inv := replacePrefix_inverse (h.labels_length.trans other.labels_length.symm)
    (h.followLabels_past hv) (other.followLabels_past hv)
  right_inv := replacePrefix_inverse (other.labels_length.trans h.labels_length.symm)
    (other.followLabels_past hv) (h.followLabels_past hv)

end Meanders.FirstCrossing
