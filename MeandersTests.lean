import MeandersTests.FirstCrossingCertificates
import MeandersTests.FirstCrossingPacked
import MeandersTests.FirstCrossingEval
import MeandersTests.FirstCrossing
import MeandersTests.FirstCrossingNative
import MeandersTests.Run
import MeandersTests.Axioms
import MeandersTests.BruteForce
import MeandersTests.Verifier

/-!
Build-time regression checks. This is a separate Lake library so that
`lake build Meanders` never runs a brute-force count; `lake test` builds it.
`#guard` evaluates with the compiler, so nothing here uses `native_decide`
or adds an axiom, and nothing in `Meanders` may import it.
-/
