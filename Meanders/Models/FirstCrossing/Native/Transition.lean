import Meanders.Models.FirstCrossing.Native.State

/-!
# Native First-Crossing transition

Each move inserts an incidence cup, attaches the original owner steps, and
joins newly forced ordinal pairs in P-then-Q order. Only one final cycle is
accepted. The lower observer is attached after this weight-independent surgery.
-/

namespace Meanders.FirstCrossing

/-- Four raw labels; collisions never identify their contributions. -/
inductive Move
  | UU | UD | DU | DD
  deriving DecidableEq, Repr, BEq

/-- Fixed reference label order. -/
def Move.all : List Move := [.UU, .UD, .DU, .DD]

/-- Whether the upper owner takes its original down step. -/
def Move.upperDown : Move → Bool
  | .UU | .UD => false
  | .DU | .DD => true

/-- Whether the lower owner takes its original down step. -/
def Move.lowerDown : Move → Bool
  | .UU | .DU => false
  | .UD | .DD => true

/-- Original counters are changed only by the two labelled physical steps. -/
def moveCounters (c : Counters) (side : Side) (m : Move) : Counters :=
  let p := Group.onSide true side
  let q := Group.onSide false side
  (c.set p (c.get p + m.upperDown.toNat)).set q (c.get q + m.lowerDown.toNat)

/-- Scratch incidence paths retain their temporary endpoint names until normalization. -/
structure Splice where
  /-- Current four oldest-first port groups. -/
  ports : Ports
  /-- A consumed incidence is `none`; a live incidence stores its named mate. -/
  mate : List (Option ℕ)
  /-- Number of cycles closed during this one physical step. -/
  cycles : ℕ
  deriving DecidableEq, Repr

/-- Join two incidences, either splicing their paths or recording a completed cycle. -/
def spliceJoin (w : Splice) (x y : ℕ) : Option Splice := do
  if x == y then failure
  let a ← (w.mate[x]?).join
  let b ← (w.mate[y]?).join
  if w.mate[a]? != some (some x) || w.mate[b]? != some (some y) then failure
  let mate := (w.mate.set x none).set y none
  if a == y then
    if b == x then return { w with mate, cycles := w.cycles + 1 } else failure
  else
    if b == x || a == b then failure
    return { w with mate := (mate.set a (some b)).set b (some a) }

/-- A physical owner edge attaches to a reservoir top or extends that reservoir. -/
def attachOwner (w : Splice) (g : Group) (down : Bool) (cup : ℕ) : Option Splice :=
  if down then
    match (w.ports.get g).reverse with
    | [] => none
    | x :: xs => spliceJoin { w with ports := w.ports.set g xs.reverse } x cup
  else some { w with ports := w.ports.set g (w.ports.get g ++ [cup]) }

/-- One owner drains forced ordinal pairs from both FIFO heads, oldest first. -/
def drain : ℕ → Group → Group → Splice → Option Splice
  | 0, _, _, w => some w
  | k + 1, left, right, w => do
    let x ← (w.ports.get left).head?
    let y ← (w.ports.get right).head?
    let ports := (w.ports.set left (w.ports.get left).tail).set right
      (w.ports.get right).tail
    let w ← spliceJoin { w with ports } x y
    if !cyclicCheck w.mate w.ports.cyclic [] then failure
    drain k left right w

/-- Drop temporary names and renumber in fixed owner/side storage order. -/
def normalizeMate (w : Splice) : Option (List ℕ) := do
  let flat := w.ports.flat
  if !decide flat.Nodup then failure
  if w.mate.countP Option.isSome != flat.length then failure
  let mate ← flat.mapM fun x => do
    let y ← (w.mate[x]?).join
    if flat.contains y then some (flat.idxOf y) else none
  return mate

/-- Counter attachment does not alter the geometric normalization. -/
def normalize (c : Counters) (w : Splice) : Option Key :=
  (normalizeMate w).map (Key.mk c)

/-- Normalization preserves every original down counter. -/
theorem normalize_counters {c : Counters} {w : Splice} {y : Key}
    (h : normalize c w = some y) : y.counters = c := by
  unfold normalize at h
  cases hw : normalizeMate w with
  | none => simp [hw] at h
  | some pairing =>
    simp only [hw, Option.map_some, Option.some.injEq] at h
    cases h
    rfl

/-- All local feasibility guards use original counters and unconsumed down budgets. -/
def moveAllowed (s : RunSpec) (t : Stage) (x : Key) (side : Side) (m : Move) : Bool :=
  let g := geometry s t x.counters
  let c := moveCounters x.counters side m
  let p := Group.onSide true side
  let q := Group.onSide false side
  (!m.upperDown || decide (0 < g.reservoir.get p)) &&
    (!m.lowerDown || decide (0 < g.reservoir.get q)) &&
    decide (t.processed side < s.sideLength side) &&
    [p, q].all (fun owner => decide (c.get owner ≤ s.budgets.get owner ∧
      s.budgets.get owner - c.get owner ≤ s.sideLength side - t.processed side - 1)) &&
    (match side with | .left => prefixAllowed s (t.next side) c | .right => true)

/-- Physical surgery and deterministic drains before final raw-key validation. -/
def candidateSplice (s : RunSpec) (t : Stage) (x : Key) (side : Side) (m : Move) :
    Option Splice := do
  if !moveAllowed s t x side m then failure
  let g := geometry s t x.counters
  let c := moveCounters x.counters side m
  let next := t.next side
  let offset := x.mate.length
  let w : Splice := ⟨Ports.ofLengths g.length,
    x.mate.map some ++ [some (offset + 1), some offset], 0⟩
  let w ← attachOwner w (Group.onSide true side) m.upperDown offset
  let w ← attachOwner w (Group.onSide false side) m.lowerDown (offset + 1)
  if !cyclicCheck w.mate w.ports.cyclic [] then failure
  let w ← match s.sector with
    | .low => some w
    | .high _ _ _ => do
      let new := geometry s next c
      let pOld := min g.emitted.pl g.emitted.pr
      let pNew := min new.emitted.pl new.emitted.pr
      let qOld := min g.emitted.ql g.emitted.qr
      let qNew := min new.emitted.ql new.emitted.qr
      if pNew < pOld || qNew < qOld then failure
      let w ← drain (pNew - pOld) .pl .pr w
      let w ← drain (qNew - qOld) .ql .qr w
      if w.ports.lengths != new.length then failure
      some w
  if 0 < w.cycles then
    if !decide (w.cycles = 1 ∧ next.tick = 2 * s.n ∧ w.ports.flat = []) then failure
  return w

/-- Canonical key following the physical splice and all deterministic drains. -/
def candidate (s : RunSpec) (t : Stage) (x : Key) (side : Side) (m : Move) : Option Key :=
  (candidateSplice s t x side m).bind (normalize (moveCounters x.counters side m))

/-- Endpoint surgery never updates original counters a second time. -/
theorem candidate_counters {s : RunSpec} {t : Stage} {x y : Key} {side : Side} {m : Move}
    (h : candidate s t x side m = some y) :
    y.counters = moveCounters x.counters side m := by
  unfold candidate at h
  cases hw : candidateSplice s t x side m with
  | none => simp [hw] at h
  | some w =>
    simp only [hw, Option.bind_some] at h
    exact normalize_counters h

/-- Weight-independent checked native successor, with side fixed by the schedule. -/
def rawStep (s : RunSpec) (t : Stage) (x : Key) (m : Move) : Option Key :=
  if validKey s t x then
    match s.schedule[t.tick]? with
    | none => none
    | some side => match candidate s t x side m with
      | none => none
      | some y => if validKey s (t.next side) y then some y else none
  else none

/-- The lower event reads original height before any physical move or FIFO join. -/
def lowerIncrement (t : Stage) (x : Key) (m : Move) (side : Side) : ℕ :=
  if m.lowerDown && (t.processed side - 2 * x.counters.get (Group.onSide false side) == 1)
    then 1 else 0

/-- One native labelled edge with its separate lower-return increment. -/
def step (s : RunSpec) (t : Stage) (x : Key) (m : Move) : Option (Key × ℕ) := do
  let side ← s.schedule[t.tick]?
  let y ← rawStep s t x m
  return (y, lowerIncrement t x m side)

/-- Every surviving successor passes the explicit next-stage raw checks. -/
theorem rawStep_valid {s : RunSpec} {t : Stage} {x y : Key} {m : Move}
    (h : rawStep s t x m = some y) :
    ∃ side, s.schedule[t.tick]? = some side ∧ validKey s (t.next side) y = true := by
  unfold rawStep at h
  split at h
  · cases hs : s.schedule[t.tick]? with
    | none => simp [hs] at h
    | some side =>
      simp only [hs] at h
      cases hc : candidate s t x side m with
      | none => simp [hc] at h
      | some z =>
        simp only [hc] at h
        split at h
        · cases h
          exact ⟨side, rfl, by assumption⟩
        · contradiction
  · contradiction

/-- A surviving raw step changes precisely the two original labelled counters. -/
theorem rawStep_counters {s : RunSpec} {t : Stage} {x y : Key} {m : Move}
    (h : rawStep s t x m = some y) :
    ∃ side, s.schedule[t.tick]? = some side ∧
      y.counters = moveCounters x.counters side m := by
  unfold rawStep at h
  split at h
  · cases hs : s.schedule[t.tick]? with
    | none => simp [hs] at h
    | some side =>
      simp only [hs] at h
      cases hc : candidate s t x side m with
      | none => simp [hc] at h
      | some z =>
        simp only [hc] at h
        split at h
        · cases h
          exact ⟨side, rfl, candidate_counters hc⟩
        · contradiction
  · contradiction

/-- Each lower-return event is a single indicator. -/
theorem lowerIncrement_le_one (t : Stage) (x : Key) (m : Move) (side : Side) :
    lowerIncrement t x m side ≤ 1 := by
  unfold lowerIncrement
  split <;> omega

end Meanders.FirstCrossing
