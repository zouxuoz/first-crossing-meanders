import Meanders.Algorithms.FirstCrossing
import Meanders.Algorithms.BruteForce
import Meanders.Certify.Schema

/-!
# The registry of proved evaluators

A checker may only run a counter that is proved to compute the specification.
`ProvedEvaluator p` bundles a counter for problem `p` with that proof, and
`evaluator` is the table from `(Algorithm, Problem)` to one: the single place
that records which algorithm is certified for which problem.

This is why there is one count checker rather than one per algorithm and
problem: `Meanders.Certify.CountCertificate.check` looks the pair up here,
and its soundness comes from the `correct` field.
-/

namespace Meanders.Certify

/-- A counter for problem `p` together with the proof that it computes the
specification `p.number`. -/
structure ProvedEvaluator (p : Problem) where
  /-- The counter. -/
  count : ℕ → ℕ
  /-- It computes the specification. -/
  correct : ∀ n, count n = p.number n

/-- The registry: the proved evaluator the checker runs for a tag pair. -/
def evaluator : Algorithm → (p : Problem) → ProvedEvaluator p
  | .firstCrossing, p | .firstCrossingOptimized, p =>
    ⟨FirstCrossing.count p, FirstCrossing.count_eq p⟩
  | .bruteForce, p => ⟨BruteForce.count p, BruteForce.count_eq p⟩

end Meanders.Certify
