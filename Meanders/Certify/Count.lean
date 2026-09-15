import Meanders.Certify.Evaluators

/-!
# Count certificates

The weakest possible certificate: a claim that `p.number n` equals some
number, with no evidence attached beyond the name of the evaluator that
produced it. It is checkable at all because the registry
`Meanders.Certify.evaluator` holds a counter proved to compute `p.number`
for that pair — the Lean side simply recomputes and compares.

That makes this certificate kind *sound but not scalable*: verifying costs as
much as computing. It pins down the shape every certificate kind has: a
`Correct` proposition stated against the specification, a `check` that runs,
and `check_sound` joining them. The layered First-Crossing certificate,
checked against the proved transition function, satisfies the same three.
-/

namespace Meanders.Certify

/-- The common statement established by every accepted certificate kind. -/
structure Claim where
  /-- The counting problem. -/
  problem : Problem
  /-- The order. -/
  n : ℕ
  /-- The claimed number of objects of that order. -/
  count : ℕ
deriving Repr, DecidableEq

/-- A claim is correct when it states the specification's cardinality. -/
def Claim.Correct (c : Claim) : Prop := c.count = c.problem.number c.n

/-- A claim that there are `count` meanders of order `n` for `problem`,
computed by `algorithm`. -/
structure CountCertificate where
  /-- The problem. -/
  problem : Problem
  /-- The evaluator that produced the count. -/
  algorithm : Algorithm
  /-- The order. -/
  n : ℕ
  /-- The claimed number of meanders of that order. -/
  count : ℕ
deriving Repr, DecidableEq

namespace CountCertificate

/-- Forget evaluator metadata and retain the mathematical claim. -/
def claim (c : CountCertificate) : Claim :=
  { problem := c.problem, n := c.n, count := c.count }

/-- What it means for a count certificate to be correct: the claim is the
specification's cardinality, not merely the output of some program. -/
def Correct (c : CountCertificate) : Prop := c.claim.Correct

/-- The checker: look the evaluator up in the registry, recompute with it, and
compare. -/
def check (c : CountCertificate) : Bool :=
  (evaluator c.algorithm c.problem).count c.n == c.count

/-- **Soundness**: if the checker accepts, the claimed count really is the
specification. This is what lets a certificate emitted by unverified Rust be
trusted without trusting the Rust. -/
theorem check_sound (c : CountCertificate) (h : c.check = true) : c.Correct := by
  unfold check at h
  rw [Correct, claim, Claim.Correct, ← (evaluator c.algorithm c.problem).correct]
  exact (beq_iff_eq.1 h).symm

/-- **Completeness**: the checker rejects nothing correct, so a rejection is
always a real defect in the certificate. -/
theorem check_complete (c : CountCertificate) (h : c.Correct) : c.check = true := by
  unfold check
  rw [Correct, claim, Claim.Correct, ← (evaluator c.algorithm c.problem).correct] at h
  exact beq_iff_eq.2 h.symm

theorem check_iff (c : CountCertificate) : c.check = true ↔ c.Correct :=
  ⟨c.check_sound, c.check_complete⟩

end CountCertificate

end Meanders.Certify
