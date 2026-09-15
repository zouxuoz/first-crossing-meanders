import Meanders.Problems.Problem
import Meanders.Core.Permutation.FiniteSupport

/-!
# The brute-force counter

The most obvious algorithm there is: filter the finite type of candidates by
a decision procedure and take its cardinality.

For closed meanders the candidates are the `catalan n` squared pairs of
noncrossing perfect matchings and the test is the flood fill
`isConnectedUnion`, feasible only to about `n = 8`.
`countClosedMeanders_eq_closedMeanderNumber` is the theorem that it computes
the specification, and it is the shape every later algorithm's correctness
theorem takes.

Open diagrams use odd compactification or even exterior cuts. The even counter
flood-fills each matching pair once and weights a connected pair by the number
of exterior lower arches, avoiding a separate cut-graph test for every arch.

`BruteForce.count` and `BruteForce.count_eq` are the algorithm's face towards
the certificate layer: one counter per supported `Problem`, each proved equal
to `Problem.number`. A new problem is one more match arm in each.
-/

namespace Meanders

/-! ## Closed meanders -/

variable {n : ℕ}

/-- **The brute-force closed-meander counter.** Enumerates the `catalan n`
squared pairs and flood-fills each union graph. -/
def countClosedMeanders (n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : NoncrossingMatching n × NoncrossingMatching n => isConnectedUnion p =
    true).card

/-- **Correctness of the counter.** -/
theorem countClosedMeanders_eq_closedMeanderNumber (n : ℕ) :
    countClosedMeanders n = closedMeanderNumber n := by
  rw [closedMeanderNumber_eq_card_filter]
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isConnectedUnion_iff p

/-! ## Open meanders -/

/-- Count connected matching pairs, weighted by their exterior lower arches.
Connectivity is flood-filled once per pair, before counting the possible cuts. -/
def countMarkedClosedMeanders (n : ℕ) : ℕ :=
  ∑ p : NoncrossingMatching n × NoncrossingMatching n,
    if isConnectedUnion p then p.2.exteriorArches.card else 0

theorem countMarkedClosedMeanders_eq (n : ℕ) :
    countMarkedClosedMeanders n = ∑ p : ClosedMeander n, p.val.2.exteriorArches.card := by
  change countMarkedClosedMeanders n =
    ∑ p : {p : NoncrossingMatching n × NoncrossingMatching n // (unionGraph p).Connected},
      p.val.2.exteriorArches.card
  rw [countMarkedClosedMeanders, Permutation.sum_subtype_eq_sum_ite
    (fun p : NoncrossingMatching n × NoncrossingMatching n => (unionGraph p).Connected)
    (fun p => p.2.exteriorArches.card)]
  apply Finset.sum_congr rfl
  intro p _
  simp only [isConnectedUnion_iff]

/-- Enumerate odd diagrams by compactification and even diagrams by exterior cuts.
The crossing-free line contributes one. -/
def countOpenMeanders (q : ℕ) : ℕ :=
  if q = 0 then 1 else if q % 2 = 1 then countClosedMeanders (q / 2 + 1)
  else countMarkedClosedMeanders (q / 2)

/-- The explicit enumeration computes the unchanged geometric specification. -/
theorem countOpenMeanders_eq_openMeanderNumber (q : ℕ) :
    countOpenMeanders q = openMeanderNumber q := by
  unfold countOpenMeanders
  split_ifs with hzero hodd
  · subst q
    exact openMeanderNumber_zero.symm
  · rw [countClosedMeanders_eq_closedMeanderNumber,
      ← openMeanderNumber_odd]
    congr 1
    omega
  · rw [countMarkedClosedMeanders_eq, ← openMeanderNumber_even (by omega : 0 < q / 2)]
    congr 1
    omega

/-! ## The algorithm, by problem -/

namespace BruteForce

/-- Brute force for each problem, using flood-fill connectivity. -/
def count : Problem → ℕ → ℕ
  | .closed => countClosedMeanders
  | .open => countOpenMeanders

/-- Brute force computes the specification of every problem it supports. -/
theorem count_eq (p : Problem) (n : ℕ) : count p n = p.number n := by
  cases p with
  | closed => exact countClosedMeanders_eq_closedMeanderNumber n
  | «open» => exact countOpenMeanders_eq_openMeanderNumber n

end BruteForce

end Meanders
