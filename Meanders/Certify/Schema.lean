import Meanders.Problems.Problem

/-!
# Certificate schema tags

The `problem` and `algorithm` fields of a certificate are enumerations
rather than raw strings, on both sides of the Rust/Lean boundary: `Problem`
mirrors the Rust `Problem` and `Algorithm` mirrors `certify::Algorithm`.
Adding a problem or an evaluator is a new constructor here, a new variant
there, and one line in the registry `Meanders.Certify.evaluator`; nothing
else changes. The fixtures in `fixtures/certificates/` are the contract test
for both sides.
-/

namespace Meanders.Certify

/-- The JSON tag of a problem, shared with the Rust `Problem`. -/
def _root_.Meanders.Problem.tag : Problem → String
  | .closed => "closed"
  | .open => "open"

/-- Parse the JSON tag of a problem. -/
def _root_.Meanders.Problem.ofTag? (s : String) : Option Problem :=
  Problem.all.find? (·.tag = s)

/-- Which evaluator produced a certificate. -/
inductive Algorithm
  /-- The brute-force enumerator: every candidate, tested one by one. -/
  | bruteForce
  /-- Shared First-Crossing reference. -/
  | firstCrossing
  /-- Packed First-Crossing producer, checked with the shared reference proof. -/
  | firstCrossingOptimized
deriving DecidableEq, Repr

/-- Every algorithm, in a fixed order. -/
def Algorithm.all : List Algorithm :=
  [.bruteForce, .firstCrossing, .firstCrossingOptimized]

/-- The JSON tag of an algorithm, shared with the Rust `certify::Algorithm`. -/
def Algorithm.tag : Algorithm → String
  | .firstCrossing => "first_crossing"
  | .firstCrossingOptimized => "first_crossing_optimized"
  | .bruteForce => "brute_force"

/-- Both First-Crossing producers share the same proved recurrence and row semantics. -/
def Algorithm.isFirstCrossing : Algorithm → Bool
  | .firstCrossing | .firstCrossingOptimized => true
  | _ => false

/-- Parse the JSON tag of an algorithm. -/
def Algorithm.ofTag? (s : String) : Option Algorithm :=
  Algorithm.all.find? (·.tag = s)

end Meanders.Certify
