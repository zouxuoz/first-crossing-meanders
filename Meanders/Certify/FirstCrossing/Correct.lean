import Meanders.Certify.FirstCrossing.Check

/-! Public soundness from exact sector replay and the proved native/source bijection. -/
namespace Meanders.Certify.FirstCrossingRun

open FirstCrossing

/-- A positive structurally valid manifest uses an admissible first-height threshold. -/
theorem Metadata.validate_threshold {m : Metadata} (h : m.validate = .ok ())
    (hn : m.nativeOrder ≠ 0) : 0 < m.threshold ∧ m.threshold ≤ m.nativeOrder := by
  unfold Metadata.validate at h
  simp only [hn, ↓reduceIte] at h
  split at h
  · change Except.error "invalid First-Crossing threshold" = Except.ok () at h
    cases h
  · rename_i hg
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hg
    omega

/-- Structural checking gives the exact explicit public-zero summary. -/
theorem Metadata.validate_zero {m : Metadata} (h : m.validate = .ok ())
    (hn : m.nativeOrder = 0) : m.closed = 0 ∧ m.openEven = 1 := by
  unfold Metadata.validate at h
  simp only [hn, ↓reduceIte] at h
  split at h
  · cases h
  · rename_i hg
    simp only [Bool.or_eq_true, Bool.not_eq_true, bne_iff_ne, not_or, not_not] at hg
    exact ⟨hg.1.1.2, hg.1.2⟩

/-- Successful reference replay retains structural metadata validation. -/
theorem check_valid {m : Metadata} {layers : List FirstCrossing.Layer} {result : Counts}
    (h : check m layers = .ok result) : m.validate = .ok () := by
  unfold check checkWith at h
  cases hl : m.validateLayerCount layers.length with
  | error e => simp [hl] at h
  | ok value =>
    cases value
    simp only [hl] at h
    cases hv : m.validate with
    | error e => simp [hv] at h
    | ok value => cases value; rfl

/-- The checked joint result has the unchanged public Closed/even Open meaning. -/
theorem check_joint_correct {m : Metadata} {layers : List FirstCrossing.Layer} {result : Counts}
    (h : check m layers = .ok result) :
    result = (closedMeanderNumber m.nativeOrder, openMeanderNumber (2 * m.nativeOrder)) := by
  have hv := check_valid h
  have hr := check_sound h
  by_cases hn : m.nativeOrder = 0
  · have he := evaluate_correct 0
    have hz : (0, 1) = (closedMeanderNumber 0, openMeanderNumber (2 * 0)) :=
      Prod.ext he.1 he.2
    simpa [hn] using hr.trans (by simpa [hn] using hz)
  · have ht := Metadata.validate_threshold hv hn
    rw [ite_eq_right hn] at hr
    exact hr.trans (evaluateJoint_correct (Nat.pos_of_ne_zero hn) ht.1 ht.2)

/-- Exact replay returns the pair bound in the manifest, including the zero convention. -/
theorem check_claimed {m : Metadata} {layers : List FirstCrossing.Layer} {result : Counts}
    (h : check m layers = .ok result) : result = (m.closed, m.openEven) := by
  have hv := check_valid h
  by_cases hn : m.nativeOrder = 0
  · have hz := Metadata.validate_zero hv hn
    simpa [hn, hz.1, hz.2] using check_sound h
  · unfold check checkWith at h
    cases hl : m.validateLayerCount layers.length with
    | error e => simp [hl] at h
    | ok value =>
      cases value
      simp only [hl, hv, hn, ↓reduceIte] at h
      split at h
      · cases h
      · split at h
        · cases h; assumption
        · cases h

/-- The existing public claim selects a correctly checked ordinary or lower channel. -/
theorem Metadata.validateClaim_sound {m : Metadata} {c : Claim}
    (hc : m.validateClaim c = .ok ())
    (hj : (m.closed, m.openEven) =
      (closedMeanderNumber m.nativeOrder, openMeanderNumber (2 * m.nativeOrder))) : c.Correct := by
  have hclosed : m.closed = closedMeanderNumber m.nativeOrder := congrArg Prod.fst hj
  have hopen : m.openEven = openMeanderNumber (2 * m.nativeOrder) := congrArg Prod.snd hj
  cases c with
  | mk p n count =>
    cases p with
    | closed =>
      simp only [Metadata.validateClaim] at hc
      split at hc
      · cases hc
      · rename_i hg
        simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_not] at hg
        change count = closedMeanderNumber n
        simpa [hg.1, hg.2] using hclosed
    | «open» =>
      simp only [Metadata.validateClaim] at hc
      split at hc
      · rename_i hn
        split at hc
        · cases hc
        · rename_i hg
          simp only [bne_iff_ne, not_not] at hg
          change count = openMeanderNumber n
          simpa [hn, hg] using hopen
      · split at hc
        · rename_i hg
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hg
          split at hc
          · cases hc
          · rename_i hv
            simp only [bne_iff_ne, not_not] at hv
            change count = openMeanderNumber n
            have hi := openMeanderNumber_odd (m.nativeOrder - 1)
            have hi₁ : 2 * (m.nativeOrder - 1) + 1 = n := by omega
            have hi₂ : m.nativeOrder - 1 + 1 = m.nativeOrder := by omega
            rw [hi₁, hi₂] at hi
            exact hv.trans (hclosed.trans hi.symm)
        · cases hc

/-- A loaded First-Crossing table carries only canonical metadata and exact parsed layers. -/
structure Certificate where
  /-- Unchanged public problem and count. -/
  claim : Claim
  /-- Complete ordered source metadata and separate summary channels. -/
  metadata : Metadata
  /-- Actual sector-major layers, including every seed and terminal. -/
  layers : List FirstCrossing.Layer
  deriving Repr

/-- Accept a public claim only after exact sector replay and public convention checks. -/
def Certificate.claimWith (sectorCheck : RunSpec → List FirstCrossing.Layer →
    FirstCrossingSectorTable.Summary → Except String FirstCrossingSectorTable.Summary)
    (c : Certificate) : Except String Claim :=
  match checkWith sectorCheck c.metadata c.layers with
  | .error e => .error e
  | .ok _ => match c.metadata.validateClaim c.claim with
    | .error e => .error e
    | .ok () => .ok c.claim

/-- Public certificate checking always chooses the actual native reference recurrence. -/
abbrev Certificate.claim? := Certificate.claimWith FirstCrossingSectorTable.check

/-- Full numerical soundness; SHA and structural commitment checks are not premises. -/
theorem Certificate.claim?_sound {c : Certificate} {claim : Claim}
    (h : c.claim? = .ok claim) : claim.Correct := by
  unfold Certificate.claim? Certificate.claimWith at h
  cases hr : check c.metadata c.layers with
  | error e => simp [hr] at h
  | ok result =>
    simp only [hr] at h
    cases hc : c.metadata.validateClaim c.claim with
    | error e => simp [hc] at h
    | ok value =>
      cases value
      simp only [hc, Except.ok.injEq] at h
      subst claim
      exact Metadata.validateClaim_sound hc ((check_claimed hr).symm.trans (check_joint_correct hr))

end Meanders.Certify.FirstCrossingRun
