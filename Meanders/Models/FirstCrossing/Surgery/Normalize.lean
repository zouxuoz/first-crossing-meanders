import Meanders.Models.FirstCrossing.Surgery.Splice
import Meanders.Models.FirstCrossing.Native.Codec

/-!
# Exact normalization of named live mates

Normalization renumbers the distinct live names in `ports.flat` storage order.
These proofs use the actual `mapM`/`idxOf` implementation. No checked-output
pairing predicate is assumed.
-/

namespace Meanders.FirstCrossing

/-- All and only the currently live scratch names occur in the four port groups. -/
def CoversLive (w : Splice) : Prop := ∀ x, x ∈ w.ports.flat ↔ Live w.mate x

private theorem mapM_lookup {f : ℕ → Option ℕ} {xs ys : List ℕ}
    (h : xs.mapM f = some ys) :
    xs.length = ys.length ∧ ∀ (i x : ℕ), xs[i]? = some x → ys[i]? = f x := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst ys
    simp
  | cons a xs ih =>
    cases ha : f a with
    | none => simp [List.mapM_cons, ha] at h
    | some b =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons, ha, ht] at h
      | some zs =>
        have he : b :: zs = ys := by simpa [List.mapM_cons, ha, ht] using h
        subst ys
        obtain ⟨hlen, hlookup⟩ := ih ht
        constructor
        · simp [hlen]
        · intro i x hx
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
            subst x
            simpa using ha.symm
          | succ i =>
            exact hlookup i x (by simpa using hx)

/-- The exact rename calculation for one old named endpoint. -/
def renameMate (w : Splice) (x : ℕ) : Option ℕ := do
  let y ← (w.mate[x]?).join
  if w.ports.flat.contains y then some (w.ports.flat.idxOf y) else none

/-- A successful normalization traversed exactly the fixed storage-order names. -/
theorem normalizeMate_traversal {w : Splice} {ys : List ℕ}
    (h : normalizeMate w = some ys) : w.ports.flat.mapM (renameMate w) = some ys := by
  simp only [normalizeMate] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · change List.mapM (fun x => ((w.mate[x]?).join).bind fun y =>
        if w.ports.flat.contains y then some (w.ports.flat.idxOf y) else none)
        w.ports.flat = some ys
      simpa only [Option.bind_eq_bind] using h

/-- Extract the successful mate-list calculation from counter attachment. -/
theorem normalize_mate {c : Counters} {w : Splice} {out : Key}
    (h : normalize c w = some out) : normalizeMate w = some out.mate := by
  unfold normalize at h
  cases ht : normalizeMate w with
  | none => simp [ht] at h
  | some ys =>
    simp only [ht, Option.map_some, Option.some.injEq] at h
    cases h
    rfl

/-- The normalized array has exactly one slot for each listed live name. -/
theorem normalize_length {c : Counters} {w : Splice} {out : Key}
    (h : normalize c w = some out) : out.mate.length = w.ports.flat.length :=
  (mapM_lookup (normalizeMate_traversal (normalize_mate h))).1.symm

/-- Each output slot is the actual guarded old-mate/idxOf rename calculation. -/
theorem normalize_lookup {c : Counters} {w : Splice} {out : Key}
    (h : normalize c w = some out) {i x : ℕ} (hi : w.ports.flat[i]? = some x) :
    out.mate[i]? = renameMate w x :=
  (mapM_lookup (normalizeMate_traversal (normalize_mate h))).2 i x hi

/-- The position of a uniquely listed name is exactly its supplied array index. -/
theorem flat_idxOf {flat : List ℕ} (hn : flat.Nodup) {i x : ℕ}
    (h : flat[i]? = some x) : flat.idxOf x = i := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp h
  simpa only [hx] using hn.idxOf_getElem i hi

/-- A represented mate is normalized by the exact storage-order index map. -/
theorem normalize_mate_at {c : Counters} {w : Splice} {out : Key}
    (h : normalize c w = some out) (hn : w.ports.flat.Nodup)
    {i j x y : ℕ} (hi : w.ports.flat[i]? = some x) (hj : w.ports.flat[j]? = some y)
    (hxy : HasMate w.mate x y) : out.mate[i]? = some j := by
  rw [normalize_lookup h hi]
  have hy : y ∈ w.ports.flat := List.mem_iff_getElem?.mpr ⟨j, hj⟩
  have hj' := flat_idxOf hn hj
  simp [renameMate, HasMate] at hxy ⊢
  simp [hxy, hy, hj']

/-- The full output mate relation is conjugation by the ordered live-name list. -/
theorem normalize_conjugates {c : Counters} {w : Splice} {out : Key}
    (h : normalize c w = some out) (hn : w.ports.flat.Nodup)
    (hm : MateInvariant w.mate) (hc : CoversLive w)
    {i j x y : ℕ} (hi : w.ports.flat[i]? = some x) (hj : w.ports.flat[j]? = some y) :
    out.mate[i]? = some j ↔ HasMate w.mate x y := by
  constructor
  · intro hout
    have hxlive := (hc x).mp (List.mem_iff_getElem?.mpr ⟨i, hi⟩)
    obtain ⟨a, hxa⟩ := hxlive
    have ha : a ∈ w.ports.flat := (hc a).mpr ⟨x, hm.symm hxa⟩
    have hia := normalize_mate_at h hn hi (List.getElem?_idxOf ha) hxa
    have he : w.ports.flat.idxOf a = j := Option.some.inj (hia.symm.trans hout)
    have hname := List.getElem?_idxOf ha
    rw [he, hj] at hname
    have hay : y = a := Option.some.inj hname
    simpa only [hay] using hxa
  · exact normalize_mate_at h hn hi hj

/-- Normalization preserves fixed-point-free involution, without checking it afterward. -/
theorem normalize_pairingValid {c : Counters} {w : Splice} {out : Key}
    (h : normalize c w = some out) (hn : w.ports.flat.Nodup)
    (hm : MateInvariant w.mate) (hc : CoversLive w) : pairingValid out.mate = true := by
  rw [pairingValid_iff]
  intro i hi
  have hi' : i < w.ports.flat.length := by simpa only [normalize_length h] using hi
  let x := w.ports.flat[i]
  have hix : w.ports.flat[i]? = some x := List.getElem?_eq_getElem hi'
  obtain ⟨a, hxa⟩ := (hc x).mp (List.mem_iff_getElem?.mpr ⟨i, hix⟩)
  have ha : a ∈ w.ports.flat := (hc a).mpr ⟨x, hm.symm hxa⟩
  let j := w.ports.flat.idxOf a
  have hja : w.ports.flat[j]? = some a := List.getElem?_idxOf ha
  refine ⟨j, normalize_mate_at h hn hix hja hxa, ?_,
    normalize_mate_at h hn hja hix (hm.symm hxa)⟩
  intro hij
  rw [hij, hja] at hix
  have hax : a = x := Option.some.inj hix
  exact (hm x a hxa).1 hax.symm

/-- Equal listed names have exactly equal storage indices under distinctness. -/
theorem flat_names_eq_iff {flat : List ℕ} (hn : flat.Nodup) {i j x y : ℕ}
    (hi : flat[i]? = some x) (hj : flat[j]? = some y) : x = y ↔ i = j := by
  constructor
  · intro hxy
    have hh := flat_idxOf hn hi
    rw [hxy, flat_idxOf hn hj] at hh
    exact hh.symm
  · intro hij
    subst j
    exact Option.some.inj (hi.symm.trans hj)

/-- Map a normalized storage index back to its old physical incidence.
The fallback is irrelevant on the output domain, whose length is proved exact. -/
def normalizedPort {V : Type*} (w : Splice) (port : ℕ → V) (i : ℕ) : V :=
  port ((w.ports.flat[i]?).getD 0)

/-- On a listed name the physical relabelling has no fallback. -/
theorem normalizedPort_eq {V : Type*} {w : Splice} {port : ℕ → V} {i x : ℕ}
    (hi : w.ports.flat[i]? = some x) : normalizedPort w port i = port x := by
  simp [normalizedPort, hi]

/-- Every pair of output storage slots retains exactly its original physical paths. -/
theorem normalize_paths {V : Type*} {c : Counters} {w : Splice} {out : Key}
    {G : SimpleGraph V} {port : ℕ → V}
    (h : normalize c w = some out) (hn : w.ports.flat.Nodup)
    (hm : MateInvariant w.mate) (hc : CoversLive w)
    (hp : RepresentsLivePaths w.mate G port) {i j : ℕ}
    (hi : i < out.mate.length) (hj : j < out.mate.length) :
    G.Reachable (normalizedPort w port i) (normalizedPort w port j) ↔
      i = j ∨ out.mate[i]? = some j := by
  have hi' : i < w.ports.flat.length := by simpa only [normalize_length h] using hi
  have hj' : j < w.ports.flat.length := by simpa only [normalize_length h] using hj
  let x := w.ports.flat[i]
  let y := w.ports.flat[j]
  have hix : w.ports.flat[i]? = some x := List.getElem?_eq_getElem hi'
  have hjy : w.ports.flat[j]? = some y := List.getElem?_eq_getElem hj'
  have hx := (hc x).mp (List.mem_iff_getElem?.mpr ⟨i, hix⟩)
  have hy := (hc y).mp (List.mem_iff_getElem?.mpr ⟨j, hjy⟩)
  rw [normalizedPort_eq hix, normalizedPort_eq hjy, hp x y hx hy,
    flat_names_eq_iff hn hix hjy, normalize_conjugates h hn hm hc hix hjy]

/-- Lifting a raw array to scratch `some` entries changes no mate lookup. -/
theorem hasMate_map_some {mate : List ℕ} {i j : ℕ} :
    HasMate (mate.map some) i j ↔ mate[i]? = some j := by
  unfold HasMate
  rw [List.getElem?_map]
  cases mate[i]? <;> simp

/-- Normalization transports the full live-path relation to consecutive names. -/
theorem normalize_represents {V : Type*} {c : Counters} {w : Splice} {out : Key}
    {G : SimpleGraph V} {port : ℕ → V}
    (h : normalize c w = some out) (hn : w.ports.flat.Nodup)
    (hm : MateInvariant w.mate) (hc : CoversLive w)
    (hp : RepresentsLivePaths w.mate G port) :
    RepresentsLivePaths (out.mate.map some) G (normalizedPort w port) := by
  rintro i j ⟨a, hia⟩ ⟨b, hjb⟩
  have hi : i < out.mate.length := by simpa using hia.bound
  have hj : j < out.mate.length := by simpa using hjb.bound
  rw [hasMate_map_some]
  exact normalize_paths h hn hm hc hp hi hj

/-- Finite enumeration of live array indices; mate values are not used as names. -/
def liveNames (mate : List (Option ℕ)) : List ℕ :=
  ((List.finRange mate.length).filter fun i => (mate[i.val]).isSome).map Fin.val

/-- The finite index enumeration has no repetitions. -/
theorem liveNames_nodup (mate : List (Option ℕ)) : (liveNames mate).Nodup := by
  exact ((List.nodup_finRange mate.length).filter _).map Fin.val_injective

/-- The enumeration contains exactly those names whose mate lookup succeeds. -/
theorem mem_liveNames {mate : List (Option ℕ)} {x : ℕ} : x ∈ liveNames mate ↔ Live mate x := by
  simp only [liveNames, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    cases hm : mate[i.val] with
    | none => simp [hm] at hi
    | some a =>
      refine ⟨a, ?_⟩
      simp [HasMate, hm]
  · rintro ⟨a, hxa⟩
    refine ⟨⟨x, hxa.bound⟩, ?_, rfl⟩
    have hm : mate[x]'hxa.bound = some a := by
      simpa only [HasMate, List.getElem?_eq_getElem hxa.bound, Option.some.injEq] using hxa
    simp [hm]

/-- Counting present array entries equals the cardinality of their finite index list. -/
theorem liveNames_length (mate : List (Option ℕ)) :
    (liveNames mate).length = mate.countP Option.isSome := by
  have h := congrArg (List.countP Option.isSome) (List.ofFn_getElem (xs := mate))
  simpa only [liveNames, List.length_map, ← List.countP_eq_length_filter,
    List.ofFn_eq_map, List.countP_map, Function.comp_def] using h

/-- Exact coverage and distinctness discharge the executable countP guard. -/
theorem countP_eq_flat_length {w : Splice} (hn : w.ports.flat.Nodup) (hc : CoversLive w) :
    w.mate.countP Option.isSome = w.ports.flat.length := by
  have hp : w.ports.flat.Perm (liveNames w.mate) :=
    (List.perm_ext_iff_of_nodup hn (liveNames_nodup w.mate)).mpr fun x => by
      rw [mem_liveNames]
      exact hc x
  rw [← liveNames_length]
  exact hp.length_eq.symm

private theorem mapM_total {f : ℕ → Option ℕ} {xs : List ℕ}
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (fun a ha => h a (by simp [ha]))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- Every listed live endpoint finds its mate in the same exact live-name list. -/
theorem renameMate_total {w : Splice} (hm : MateInvariant w.mate) (hc : CoversLive w)
    {x : ℕ} (hx : x ∈ w.ports.flat) : ∃ j, renameMate w x = some j := by
  obtain ⟨a, hxa⟩ := (hc x).mp hx
  have ha : a ∈ w.ports.flat := (hc a).mpr ⟨x, hm.symm hxa⟩
  refine ⟨w.ports.flat.idxOf a, ?_⟩
  simp only [HasMate] at hxa
  simp [renameMate, hxa, ha]

/-- A physically valid covered frontier cannot fail any normalization guard. -/
theorem normalize_total {w : Splice} (hn : w.ports.flat.Nodup)
    (hm : MateInvariant w.mate) (hc : CoversLive w) (c : Counters) :
    ∃ out, normalize c w = some out := by
  have hcount := countP_eq_flat_length hn hc
  obtain ⟨ys, hys⟩ := mapM_total (fun x hx => renameMate_total hm hc hx)
  change List.mapM (fun x => ((w.mate[x]?).join).bind fun y =>
    if w.ports.flat.contains y then some (w.ports.flat.idxOf y) else none)
    w.ports.flat = some ys at hys
  have ht : normalizeMate w = some ys := by
    simpa [normalizeMate, hn, hcount] using hys
  exact ⟨⟨c, ys⟩, by simp [normalize, ht]⟩

end Meanders.FirstCrossing
