import Meanders.Problems.Open

/-!
# The problems

`Problem` names each counting problem the repository is about, and
`Problem.number` is its specification: the `Fintype.card` of the problem's
definition, never an algorithm. Everything downstream is stated against this
one function. An algorithm's correctness theorem says it computes
`p.number` for the problems it supports, a certificate's claim is
`count = p.number n`, and the known-value tables are indexed by `p`.

Adding a problem is one constructor here, one definition file beside this
one, and one line wherever an algorithm or table supports it. Nothing else
in the library mentions problems by name.
-/

namespace Meanders

/-- The counting problems. -/
inductive Problem
  /-- Closed meanders: a closed curve crossing a line `2n` times (OEIS A005315). -/
  | closed
  /-- Open meanders with `q` genuine crossings, including the crossing-free line. -/
  | open
deriving DecidableEq, Repr

/-- Every problem, in a fixed order. -/
def Problem.all : List Problem := [.closed, .open]

/-- The specification of each problem, as a cardinality. -/
def Problem.number : Problem → ℕ → ℕ
  | .closed => closedMeanderNumber
  | .open => openMeanderNumber

end Meanders
