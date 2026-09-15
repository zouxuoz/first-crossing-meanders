import Meanders.Algorithms.BruteForce
import Meanders.Verification.KnownValues

/-!
# Brute force against the known values

The counter must reproduce the known values of every problem it supports,
OEIS A005315 for closed and A005316 for open meanders. The
enumeration of noncrossing matchings must have Catalan-many entries — the latter checked against
`Nat.catalan`, independently of `card_noncrossingMatching_eq_catalan`, so the proof
and the computation cross-check each other.

For closed meanders `n = 7` and above are deliberately absent: brute force
costs `catalan n` squared connectivity floods, which is seconds at `n = 7`
and minutes beyond.
-/

-- This executable test module intentionally uses `#guard` assertions.
set_option linter.hashCommand false

namespace MeandersTests

open Meanders

#guard Verification.agreesWithKnown .closed (BruteForce.count .closed) 6
#guard Verification.agreesWithKnown .open (BruteForce.count .open) 8

-- Compare the explicit algorithm with the original geometric enumeration.
#guard (List.range 7).all fun q => BruteForce.count .open q == openMeanderNumber q

/-! The enumeration of noncrossing perfect matchings is Catalan-sized. -/

#guard (List.range 7).all fun n => (enumerateNoncrossingMatchings n).card == catalan n

/-! Every enumerated matching really is a noncrossing perfect matching. A
`Finset` carries repetition-freeness by construction. -/

#guard decide (∀ m : NoncrossingMatching 4, IsPerfect m.arches ∧ IsNoncrossing m.arches)

end MeandersTests
