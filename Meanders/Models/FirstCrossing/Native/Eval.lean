import Meanders.Models.FirstCrossing.Native.Transition
import Meanders.Models.FirstCrossing.Native.Stage
import Mathlib.Data.List.Sort
import Meanders.Problems.Problem

/-! Native paired reference evaluation. No source correctness is asserted here. -/
namespace Meanders.FirstCrossing

/-- Ordinary count and unbonused lower-return first moment. -/
abbrev Counts := ℕ × ℕ
/-- One complete native key with its two exact accumulated weights. -/
abbrev Row := Key × Counts
/-- A deterministically sorted, equal-key merged native frontier. -/
abbrev Layer := List Row

/-- Full deterministic sort key: four original counters followed by the mate array. -/
def Key.sortCode (x : Key) : List ℕ :=
  [x.counters.pl, x.counters.pr, x.counters.ql, x.counters.qr] ++ x.mate

theorem Key.sortCode_injective : Function.Injective Key.sortCode := by
  intro ⟨⟨a, b, c, d⟩, m⟩ ⟨⟨e, f, g, h⟩, k⟩ he
  simp only [Key.sortCode, List.cons_append, List.nil_append, List.cons.injEq] at he
  rcases he with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

/-- Lexicographic comparison, including equality. -/
def codeLE : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then codeLE as bs else decide (a < b)

/-- Add an emitted row into the current equal-key run, then advance linearly. -/
def mergeRun (row : Row) : Layer → Layer
  | [] => [row]
  | p :: ps =>
    if row.1 = p.1 then
      mergeRun (row.1, (row.2.1 + p.2.1, row.2.2 + p.2.2)) ps
    else row :: mergeRun p ps

/-- Sort all emitted rows and merge adjacent equal keys in one linear traversal. -/
def mergeRows (rows : Layer) : Layer :=
  match rows.mergeSort (fun a b => codeLE a.1.sortCode b.1.sortCode) with
  | [] => []
  | row :: rest => mergeRun row rest

/-- A labelled edge propagates ordinary mass and its lower first moment. -/
def emitMove (s : RunSpec) (t : Stage) (row : Row) (m : Move) : Layer :=
  match step s t row.1 m with
  | none => []
  | some (key, a) => [(key, (row.2.1, row.2.2 + a * row.2.1))]

/-- All four labels are emitted separately, including colliding destinations. -/
def emitRow (s : RunSpec) (t : Stage) (row : Row) : Layer :=
  Move.all.flatMap (emitMove s t row)

/-- One shared-carrier layer; neither channel changes transition acceptance. -/
def nextLayer (s : RunSpec) (t : Stage) (rows : Layer) : Layer :=
  mergeRows (rows.flatMap (emitRow s t))

/-- Only the current and successor logical layer are retained by the recursion. -/
def runLayers (s : RunSpec) : ℕ → Stage → Layer → Layer
  | 0, _, rows => rows
  | k + 1, t, rows =>
    match s.schedule[t.tick]? with
    | none => []
    | some side => runLayers s k (t.next side) (nextLayer s t rows)

/-- The terminal filter checks budgets and empty retained pairing explicitly. -/
def terminalKey (s : RunSpec) (x : Key) : Bool :=
  validKey s (Stage.ofTick s (2 * s.n)) x &&
    decide (x.counters = s.budgets ∧ x.mate = [])

/-- Unbonused terminal ordinary/lower-return totals. -/
def sectorTerminal (s : RunSpec) (rows : Layer) : Counts :=
  rows.foldl (fun total row => if terminalKey s row.1 then
    (total.1 + row.2.1, total.2 + row.2.2) else total) (0, 0)

/-- The single cut-crossing lower arch is external to the propagated jet. -/
def RunSpec.lowerBonus (s : RunSpec) : ℕ :=
  match s.sector with
  | .low => 0
  | .high _ _ v => if 0 < v then 1 else 0

/-- Evaluate one valid sector, applying the HIGH bonus once after terminal validation. -/
def runSector (s : RunSpec) : Counts :=
  if s.valid then
    let raw := sectorTerminal s (runLayers s (2 * s.n) ⟨0, 0, 0⟩ [(Key.empty, (1, 0))])
    (raw.1, raw.2 + s.lowerBonus * raw.1)
  else (0, 0)

/-- Canonical LOW-then-HIGH enumeration; source-empty admissible sectors remain. -/
def sectorSpecs (n K : ℕ) : List RunSpec :=
  (⟨n, K, .low⟩ :: (List.range (2 * n)).flatMap (fun L =>
    (List.range (min L (2 * n - L) + 1)).map (fun u =>
      (⟨n, K, .high L u (2 * K - u)⟩ : RunSpec)))).filter RunSpec.valid

/-- Every enumerated sector passes the native metadata contract. -/
theorem sectorSpecs_valid {n K : ℕ} {s : RunSpec} (h : s ∈ sectorSpecs n K) :
    s.valid = true := (List.mem_filter.mp h).2

/-- Sequential sector evaluation retains no whole-run trace. -/
def runAtThreshold (n K : ℕ) : Counts :=
  (sectorSpecs n K).foldl (fun total s =>
    let c := runSector s
    (total.1 + c.1, total.2 + c.2)) (0, 0)

/-- Shared public-size results, with no odd alias at rank zero. -/
structure Evaluation where
  /-- Public Closed count at the native rank. -/
  closed : ℕ
  /-- Public Open count at twice the native rank. -/
  openEven : ℕ
  /-- Previous odd-Open alias, absent at native rank zero. -/
  openOddPrevious : Option ℕ
  deriving DecidableEq, Repr

/-- The exact specified default threshold and public zero conventions. -/
def evaluate (n : ℕ) : Evaluation :=
  if n = 0 then ⟨0, 1, none⟩ else
    let c := runAtThreshold n (n / 2 + 1)
    ⟨c.1, c.2, some c.1⟩

end Meanders.FirstCrossing

/-! Public Closed/Open crossing conventions for the shared First-Crossing carrier. -/
namespace Meanders.FirstCrossing

/-- Closed rank or genuine open crossings. Even Open uses the lower channel directly.
The registry certifies both public problems. -/
def count : Problem → ℕ → ℕ
  | .closed, n => (evaluate n).closed
  | .open, q => if q = 0 then 1 else if q % 2 = 1 then (evaluate (q / 2 + 1)).closed
      else (evaluate (q / 2)).openEven

@[simp] theorem count_closed_zero : count .closed 0 = 0 := rfl
@[simp] theorem count_open_zero : count .open 0 = 1 := rfl

/-- Odd Open uses the ordinary value of the same associated closed rank. -/
theorem count_open_odd (n : ℕ) : count .open (2 * n + 1) = (evaluate (n + 1)).closed := by
  have hp : (2 * n + 1) % 2 = 1 := by omega
  have hd : (2 * n + 1) / 2 = n := by omega
  simp [count, hp, hd]

/-- Positive even Open uses its exact lower moment, with no symmetry division. -/
theorem count_open_even {n : ℕ} (hn : 0 < n) :
    count .open (2 * n) = (evaluate n).openEven := by
  have hz : 2 * n ≠ 0 := by omega
  simp [count, hz]

end Meanders.FirstCrossing
