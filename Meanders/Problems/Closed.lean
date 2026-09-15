import Meanders.Core.Matching.Dyck
import Meanders.Core.Overlay

/-!
# Closed meanders

A **closed meander of order `n`** is a closed curve crossing a fixed line at
`2n` points. Cutting along the line splits it into an arc system above and an
arc system below, each a noncrossing perfect matching of the `2n` crossings;
the curve is closed and connected exactly when the union of the two matchings
is a connected graph. That is the definition taken here:

  `ClosedMeander n := {p : NoncrossingMatching n × NoncrossingMatching n //
    (unionGraph p).Connected}`

and `closedMeanderNumber n := Fintype.card (ClosedMeander n)`. It is the
literature definition, written as directly as Lean allows, and it is *not*
written to be computed with — `SimpleGraph.Connected` is decidable but its
decision procedure enumerates walks.

This file is the specification of one problem; `Meanders.Problems.Problem`
lists the problems and `Problem.number` is the function every algorithm,
certificate, and known-value table is stated against. Everything that
*computes* the number lives under `Meanders.Algorithms`, and each algorithm
ends in a theorem that it equals the specification; the first is
`Meanders.countClosedMeanders_eq_closedMeanderNumber`.
-/

namespace Meanders

variable {n : ℕ}

/-- A closed meander of order `n`. -/
def ClosedMeander (n : ℕ) : Type :=
  {p : NoncrossingMatching n × NoncrossingMatching n // (unionGraph p).Connected}

instance : Fintype (ClosedMeander n) :=
  Subtype.fintype fun p => (unionGraph p).Connected

/-- **The closed-meander number** (OEIS A005315): `1, 2, 8, 42, 262, …`
for `n = 1, 2, 3, 4, 5, …`. -/
def closedMeanderNumber (n : ℕ) : ℕ := Fintype.card (ClosedMeander n)

theorem closedMeanderNumber_eq_card_filter (n : ℕ) :
    closedMeanderNumber n =
      (Finset.univ.filter fun p : NoncrossingMatching n × NoncrossingMatching n =>
        (unionGraph p).Connected).card :=
  Fintype.card_subtype _

end Meanders
