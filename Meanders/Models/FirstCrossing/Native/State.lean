import Meanders.Models.FirstCrossing.Original.Source

/-!
# Raw First-Crossing frontier state

The fixed groups are PL, PR, QL, QR, each stored oldest first. Cyclic geometric
order is `rev(PL), PR, rev(QR), QL`. Counters are original down-step counts;
forced joins never modify them. This file has no weights or exterior observer.
-/

namespace Meanders.FirstCrossing

/-- The four oriented owner/side groups, in storage order. -/
inductive Group
  | pl | pr | ql | qr
  deriving DecidableEq, Repr, BEq

/-- The complete group list in storage order. -/
def Group.all : List Group := [.pl, .pr, .ql, .qr]

/-- The physical side belonging to a group. -/
def Group.side : Group → Side
  | .pl | .ql => .left
  | .pr | .qr => .right

/-- The opposite side of the same owner. -/
def Group.other : Group → Group
  | .pl => .pr
  | .pr => .pl
  | .ql => .qr
  | .qr => .ql

/-- Upper/lower owner and a physical side determine a group. -/
def Group.onSide (upper : Bool) : Side → Group
  | .left => if upper then .pl else .ql
  | .right => if upper then .pr else .qr

/-- Four exact natural fields, also used for geometric lengths and budgets. -/
structure Counters where
  /-- Upper left quantity. -/
  pl : ℕ
  /-- Upper right quantity. -/
  pr : ℕ
  /-- Lower left quantity. -/
  ql : ℕ
  /-- Lower right quantity. -/
  qr : ℕ
  deriving DecidableEq, Repr, BEq

/-- Read one of the four fields. -/
def Counters.get (c : Counters) : Group → ℕ
  | .pl => c.pl
  | .pr => c.pr
  | .ql => c.ql
  | .qr => c.qr

/-- Change one of the four fields. -/
def Counters.set (c : Counters) (g : Group) (v : ℕ) : Counters :=
  match g with
  | .pl => { c with pl := v }
  | .pr => { c with pr := v }
  | .ql => { c with ql := v }
  | .qr => { c with qr := v }

/-- Build four concrete fields from a group-indexed calculation. -/
def Counters.ofFn (f : Group → ℕ) : Counters := ⟨f .pl, f .pr, f .ql, f .qr⟩

/-- All four fields are initially zero. -/
def Counters.zero : Counters := ⟨0, 0, 0, 0⟩

/-- Adapt the existing source-budget tuple without changing its ordering. -/
def Counters.ofTuple (c : ℕ × ℕ × ℕ × ℕ) : Counters := ⟨c.1, c.2.1, c.2.2.1, c.2.2.2⟩

@[simp] theorem Counters.get_set_same (c : Counters) (g : Group) (v : ℕ) :
    (c.set g v).get g = v := by cases g <;> rfl

@[simp] theorem Counters.get_ofFn (f : Group → ℕ) (g : Group) :
    (Counters.ofFn f).get g = f g := by cases g <;> rfl

/-- Parameters shared by every layer of one sector. -/
structure RunSpec where
  /-- Ordinary closed rank; the physical boundary has `2*n` vertices. -/
  n : ℕ
  /-- Positive first-height threshold. -/
  K : ℕ
  /-- LOW or the oriented HIGH cut and owner heights. -/
  sector : Sector
  deriving DecidableEq, Repr

/-- Exact native metadata checks, independent of any finite machine bound. -/
def RunSpec.valid (s : RunSpec) : Bool :=
  decide (0 < s.n ∧ 1 ≤ s.K ∧ s.K ≤ s.n) && match s.sector with
    | .low => true
    | .high L u v => decide (0 < L ∧ L < 2 * s.n ∧ Admissible s.n s.K L u v)

/-- The native schedule is the already specified source schedule. -/
def RunSpec.schedule (s : RunSpec) : List Side := s.sector.schedule s.n

/-- Original down budgets, in fixed owner/side order. -/
def RunSpec.budgets (s : RunSpec) : Counters := Counters.ofTuple (s.sector.budgets s.n)

/-- Number of original physical vertices belonging to each side. -/
def RunSpec.sideLength (s : RunSpec) : Side → ℕ :=
  match s.sector with
  | .low => fun side => match side with | .left => 2 * s.n | .right => 0
  | .high L _ _ => fun side => match side with | .left => L | .right => 2 * s.n - L

/-- The fixed retained-port bound, before any observer weights are attached. -/
def RunSpec.portBound (s : RunSpec) : ℕ :=
  match s.sector with
  | .low => 2 * (s.K - 1)
  | .high _ _ _ => 2 * (s.n - s.K) + 2

/-- Stage metadata shared by the layer rather than duplicated in its keys. -/
structure Stage where
  /-- Number of physical vertices already processed. -/
  tick : ℕ
  /-- Original left-side vertices already processed. -/
  left : ℕ
  /-- Original right-side vertices already processed. -/
  right : ℕ
  deriving DecidableEq, Repr, BEq

/-- The unique stage metadata at a schedule position. -/
def Stage.ofTick (s : RunSpec) (tick : ℕ) : Stage :=
  let visited := s.schedule.take tick
  ⟨tick, visited.count .left, visited.count .right⟩

/-- Original progress on a given side. -/
def Stage.processed (t : Stage) : Side → ℕ
  | .left => t.left
  | .right => t.right

/-- Visiting one physical vertex changes only that side's original progress. -/
def Stage.next (t : Stage) : Side → Stage
  | .left => ⟨t.tick + 1, t.left + 1, t.right⟩
  | .right => ⟨t.tick + 1, t.left, t.right + 1⟩

/-- Reject forged progress counters or a stage beyond the fixed schedule. -/
def Stage.valid (s : RunSpec) (t : Stage) : Bool :=
  decide (t.tick ≤ 2 * s.n ∧ t = Stage.ofTick s t.tick)

/-- Raw counter/pairing key, with consecutive names in fixed storage order. -/
structure Key where
  /-- Original down-step counters, unaffected by contractions or FIFO joins. -/
  counters : Counters
  /-- Mate position for every retained endpoint in PL,PR,QL,QR storage order. -/
  mate : List ℕ
  deriving DecidableEq, Repr, BEq

/-- One empty native history. Public rank-zero normalization belongs to counting. -/
def Key.empty : Key := ⟨Counters.zero, []⟩

/-- Geometry reconstructed from original counters at a fixed layer. -/
structure Geometry where
  /-- Original inward heights before contracting forced paths. -/
  height : Counters
  /-- Cumulative number of emitted forced-prefix endpoints on each side. -/
  emitted : Counters
  /-- Unemitted active suffix lengths. -/
  reservoir : Counters
  /-- Retained FIFO plus reservoir lengths. -/
  length : Counters
  deriving DecidableEq, Repr

/-- Exact reconstruction; `validKey` checks prerequisites of natural subtraction. -/
def geometry (s : RunSpec) (t : Stage) (c : Counters) : Geometry :=
  let h := Counters.ofFn fun g => t.processed g.side - 2 * c.get g
  match s.sector with
  | .low => ⟨h, Counters.zero, h, h⟩
  | .high _ _ _ =>
    let e := Counters.ofFn fun g => h.get g - (s.budgets.get g - c.get g)
    let r := Counters.ofFn fun g => h.get g - e.get g
    let len := Counters.ofFn fun g => r.get g + (e.get g - e.get g.other)
    ⟨h, e, r, len⟩

/-- Four lists of named endpoints, used only while performing local surgery. -/
structure Ports where
  /-- Upper left endpoints, oldest first. -/
  pl : List ℕ
  /-- Upper right endpoints, oldest first. -/
  pr : List ℕ
  /-- Lower left endpoints, oldest first. -/
  ql : List ℕ
  /-- Lower right endpoints, oldest first. -/
  qr : List ℕ
  deriving DecidableEq, Repr

/-- Read one endpoint group. -/
def Ports.get (p : Ports) : Group → List ℕ
  | .pl => p.pl
  | .pr => p.pr
  | .ql => p.ql
  | .qr => p.qr

/-- Change one endpoint group. -/
def Ports.set (p : Ports) (g : Group) (v : List ℕ) : Ports :=
  match g with
  | .pl => { p with pl := v }
  | .pr => { p with pr := v }
  | .ql => { p with ql := v }
  | .qr => { p with qr := v }

/-- Canonical consecutive endpoint names from the four decoded lengths. -/
def Ports.ofLengths (len : Counters) : Ports :=
  ⟨List.range len.pl,
    (List.range len.pr).map (len.pl + ·),
    (List.range len.ql).map (len.pl + len.pr + ·),
    (List.range len.qr).map (len.pl + len.pr + len.ql + ·)⟩

/-- Flattening uses fixed storage order. -/
def Ports.flat (p : Ports) : List ℕ := p.pl ++ p.pr ++ p.ql ++ p.qr

/-- The geometric cyclic order differs from storage order. -/
def Ports.cyclic (p : Ports) : List ℕ := p.pl.reverse ++ p.pr ++ p.qr.reverse ++ p.ql

/-- The current retained lengths. -/
def Ports.lengths (p : Ports) : Counters :=
  ⟨p.pl.length, p.pr.length, p.ql.length, p.qr.length⟩

/-- Stack check for noncrossing in a specified cyclic endpoint order. -/
def cyclicCheck (mate : List (Option ℕ)) : List ℕ → List ℕ → Bool
  | [], stack => stack.isEmpty
  | x :: xs, stack =>
    match stack with
    | y :: ys =>
      if x == y then cyclicCheck mate xs ys
      else match (mate[x]?).join with
        | none => false
        | some z => cyclicCheck mate xs (z :: stack)
    | [] => match (mate[x]?).join with
      | none => false
      | some z => cyclicCheck mate xs [z]

/-- A raw mate list must be a fixed-point-free involution on its exact domain. -/
def pairingValid (mate : List ℕ) : Bool :=
  (List.range mate.length).all fun i => match mate[i]? with
    | none => false
    | some j => decide (i ≠ j) && (mate[j]? == some i)

/-- Original counters stay within nonnegative heights and remaining down budgets. -/
def countersValid (s : RunSpec) (t : Stage) (c : Counters) : Bool :=
  Group.all.all fun g => decide (t.processed g.side ≤ s.sideLength g.side ∧
    2 * c.get g ≤ t.processed g.side ∧ c.get g ≤ s.budgets.get g ∧
    s.budgets.get g - c.get g ≤ s.sideLength g.side - t.processed g.side)

/-- The original chronological prefix filter reads counters, never retained ports. -/
def prefixAllowed (s : RunSpec) (t : Stage) (c : Counters) : Bool :=
  let grade := t.left - c.pl - c.ql
  match s.sector with
  | .low => decide (grade < s.K)
  | .high L _ _ => if t.left < L then decide (grade < s.K) else decide (grade = s.K)

/-- Complete raw-key validation, including explicit malformed-pairing rejection. -/
def validKey (s : RunSpec) (t : Stage) (x : Key) : Bool :=
  let g := geometry s t x.counters
  let ports := Ports.ofLengths g.length
  s.valid && t.valid s && countersValid s t x.counters && prefixAllowed s t x.counters &&
    decide (x.mate.length = ports.flat.length ∧ x.mate.length ≤ s.portBound ∧
      (x.mate = [] → t.tick = 0 ∨ t.tick = 2 * s.n)) &&
    pairingValid x.mate && cyclicCheck (x.mate.map some) ports.cyclic []

/-- Every valid positive metadata choice admits the native empty seed. -/
theorem initial_validKey (spec : RunSpec) (hs : spec.valid = true) :
    validKey spec ⟨0, 0, 0⟩ Key.empty = true := by
  have hs' := hs
  rcases spec with ⟨n, K, sector⟩
  cases sector with
  | low =>
    simp only [RunSpec.valid, Bool.and_eq_true, decide_eq_true_eq] at hs
    simp [validKey, hs', Key.empty, geometry, Counters.zero, Counters.get, Counters.ofFn,
      Ports.ofLengths, Ports.flat, Ports.cyclic, pairingValid, cyclicCheck, Stage.valid,
      Stage.ofTick, countersValid, prefixAllowed, Group.all, Group.side, Stage.processed,
      RunSpec.sideLength, RunSpec.budgets, Sector.budgets, Counters.ofTuple, RunSpec.portBound]
    omega
  | high L u v =>
    simp only [RunSpec.valid, Bool.and_eq_true, decide_eq_true_eq] at hs
    simp [validKey, hs', Key.empty, geometry, Counters.zero, Counters.get, Counters.ofFn,
      Ports.ofLengths, Ports.flat, Ports.cyclic, pairingValid, cyclicCheck, Stage.valid,
      Stage.ofTick, countersValid, prefixAllowed, Group.all, Group.side, Stage.processed,
      RunSpec.sideLength, RunSpec.budgets, Sector.budgets, Counters.ofTuple, RunSpec.portBound]
    split_ifs <;> omega

end Meanders.FirstCrossing

/-! The four physical seams in the concrete cyclic group order. -/

namespace Meanders.FirstCrossing

/-- Two named endpoints occur consecutively, allowing the last-to-first seam. -/
def AtSeam (w : List ℕ) (x y : ℕ) : Prop :=
  (∃ before after, w = before ++ [x, y] ++ after) ∨
    ∃ middle, w = [y] ++ middle ++ [x]

/-- Upper through joins use the oldest upper endpoints on the two sides. -/
theorem Ports.upper_fifo_seam (p : Ports) {x y : ℕ} {xs ys : List ℕ}
    (hl : p.pl = x :: xs) (hr : p.pr = y :: ys) : AtSeam p.cyclic x y := by
  left
  refine ⟨xs.reverse, ys ++ p.qr.reverse ++ p.ql, ?_⟩
  simp [Ports.cyclic, hl, hr, List.reverse_cons, List.append_assoc]

/-- Lower through joins have the opposite cyclic orientation, preserving owner identity. -/
theorem Ports.lower_fifo_seam (p : Ports) {x y : ℕ} {xs ys : List ℕ}
    (hr : p.qr = x :: xs) (hl : p.ql = y :: ys) : AtSeam p.cyclic x y := by
  left
  refine ⟨p.pl.reverse ++ p.pr ++ xs.reverse, ys, ?_⟩
  simp [Ports.cyclic, hl, hr, List.reverse_cons, List.append_assoc]

end Meanders.FirstCrossing
