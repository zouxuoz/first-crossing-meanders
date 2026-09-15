import Meanders.Problems.Closed
import Meanders.Core.Matching.Exterior
import Meanders.Core.Overlay.Cut

/-!
# Open meanders, indexed by genuine crossings

At an odd number `2n+1` of crossings the two rays are on opposite sides.
Their one-point compactification is a pair of noncrossing matchings on
`2n+2` points; the last point is at infinity, not a genuine crossing.

At an even number `2n` of crossings the rays are on the same side. Fix that
side to be lower. A diagram records its matching completion and the virtual
exterior arch joining its two rays. That arch is absent from `cutGraph`,
whose connectedness defines the open curve. Cutting an exterior arch exposes
exactly its endpoints and neither ray crosses a remaining arch. The fixed
side convention removes reflection duplication; there is no division by two.

Odd objects are defined in compactified form; their equivalence below is
an identity, not a separate theorem about embeddings or isotopy classes.
Neither definition refers to a transfer evaluator. Closing the rays gives
the equivalences below. The crossing-free open line counts once.
-/

namespace Meanders

/-- Opposite-side rays, compactified at the last point, with `2n+1` genuine crossings. -/
def OddOpenMeander (n : ℕ) : Type :=
  {p : NoncrossingMatching (n + 1) × NoncrossingMatching (n + 1) // (unionGraph p).Connected}

instance (n : ℕ) : Fintype (OddOpenMeander n) :=
  Subtype.fintype fun p => (unionGraph p).Connected

/-- Same-side lower rays on `2n` crossings; the marked arch is virtual and deleted. -/
def EvenOpenMeander (n : ℕ) : Type :=
  {d : (NoncrossingMatching n × NoncrossingMatching n) × Arch n //
    d.2 ∈ d.1.2.exteriorArches ∧ (cutGraph d.1 d.2).Connected}

instance (n : ℕ) : Fintype (EvenOpenMeander n) :=
  Subtype.fintype fun d : (NoncrossingMatching n × NoncrossingMatching n) × Arch n =>
    d.2 ∈ d.1.2.exteriorArches ∧ (cutGraph d.1 d.2).Connected

/-- A closed meander with one designated exterior lower arch. -/
abbrev MarkedClosedMeander (n : ℕ) :=
  (p : ClosedMeander n) × {a : Arch n // a ∈ p.val.2.exteriorArches}

/-- One-point compactification identifies odd open and closed diagrams. -/
def oddOpenClosedEquiv (n : ℕ) : OddOpenMeander n ≃ ClosedMeander (n + 1) := Equiv.refl _

/-- Closing two same-side rays marks an exterior arch; cutting it is the inverse. -/
def evenOpenClosedEquiv (n : ℕ) : EvenOpenMeander n ≃ MarkedClosedMeander n where
  toFun d := ⟨⟨d.val.1, (cutGraph_connected_iff d.val.1
    (d.val.1.2.mem_exteriorArches.mp d.property.1).1).mp d.property.2⟩,
    ⟨d.val.2, d.property.1⟩⟩
  invFun d := ⟨(d.1.val, d.2.val), d.2.property,
    (cutGraph_connected_iff d.1.val
      (d.1.val.2.mem_exteriorArches.mp d.2.property).1).mpr d.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Open meanders with exactly `q` genuine crossings. The empty open line counts once. -/
def OpenMeander (q : ℕ) : Type :=
  if q = 0 then Unit else if q % 2 = 1 then OddOpenMeander (q / 2) else EvenOpenMeander (q / 2)

instance (q : ℕ) : Fintype (OpenMeander q) := by
  unfold OpenMeander
  split_ifs <;> infer_instance

/-- The open-meander number, indexed by genuine crossings. -/
def openMeanderNumber (q : ℕ) : ℕ := Fintype.card (OpenMeander q)

@[simp] theorem openMeanderNumber_zero : openMeanderNumber 0 = 1 := by
  exact (Fintype.card_congr (Equiv.cast (show OpenMeander 0 = Unit by
    simp [OpenMeander]))).trans (by decide)

/-- Odd crossing counts are the corresponding closed counts. -/
theorem openMeanderNumber_odd (n : ℕ) :
    openMeanderNumber (2 * n + 1) = closedMeanderNumber (n + 1) := by
  let e : OpenMeander (2 * n + 1) ≃ OddOpenMeander n := Equiv.cast (by
    simp [OpenMeander, show (2 * n + 1) % 2 = 1 by omega,
      show (2 * n + 1) / 2 = n by omega])
  exact Fintype.card_congr (e.trans (oddOpenClosedEquiv n))

/-- Even crossing counts sum the choices of an exterior lower arch. -/
theorem openMeanderNumber_even {n : ℕ} (hn : 0 < n) :
    openMeanderNumber (2 * n) = ∑ p : ClosedMeander n, p.val.2.exteriorArches.card := by
  let e : OpenMeander (2 * n) ≃ EvenOpenMeander n := Equiv.cast (by
    simp [OpenMeander, show 2 * n ≠ 0 by omega, show 2 * n % 2 = 0 by omega,
      show 2 * n / 2 = n by omega])
  rw [openMeanderNumber, Fintype.card_congr (e.trans (evenOpenClosedEquiv n)),
    Fintype.card_sigma]
  congr 1
  funext p
  exact Fintype.card_coe _

end Meanders
