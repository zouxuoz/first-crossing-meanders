import Meanders.Core.Matching.Reflection

/-!
# Surgeries on noncrossing matchings

The moves of a boundary scan edit a noncrossing matching of the open ends at
its ends: wrap everything in a new outer arch, rotate the boundary by one
step in either direction, contract the two first points (the Temperley–Lieb
cap at the gate), or drop an outer arch. Each is built from its partner
function on `ℕ` through `NoncrossingMatching.ofNaturalPartnerFunction`, so that the conditions of
`IsPartnerFn` are arithmetic on `partnerIndex`, and each comes with the description
of its partner function that the bridge proofs use.
-/

namespace Meanders

namespace NoncrossingMatching

variable {j : ℕ}

/-! ## Facts about `partnerIndex` -/

theorem partnerIndex_noncrossing (m : NoncrossingMatching j) {x u : ℕ} (hu : u < 2 * j)
    (h₁ : x < u) (h₂ : u < m.partnerIndex x) (h₃ : m.partnerIndex x < m.partnerIndex u) : False :=
      by
  have hx : x < 2 * j := by omega
  have hpx := m.partnerIndex_lt hx
  have hpu := m.partnerIndex_lt hu
  exact m.not_interleave (x := ⟨x, hx⟩) (y := ⟨m.partnerIndex x, hpx⟩)
    (u := ⟨u, hu⟩) (v := ⟨m.partnerIndex u, hpu⟩)
    (Fin.ext (by simp [m.partnerIndex_eq hx])) (Fin.ext (by simp [m.partnerIndex_eq hu])) h₁ h₂ h₃

theorem partnerIndex_injective (m : NoncrossingMatching j) {x u : ℕ} (hx : x < 2 * j)
    (hu : u < 2 * j)
    (h : m.partnerIndex x = m.partnerIndex u) : x = u := by
  rw [← m.partnerIndex_partnerIndex hx, h, m.partnerIndex_partnerIndex hu]

/-! ## Building a matching from an `ℕ`-valued partner function -/

/-- The conditions for `g` to be the `partnerIndex` of a matching of rank `j`. -/
structure IsNaturalPartnerFunction (j : ℕ) (g : ℕ → ℕ) : Prop where
  lt : ∀ i, i < 2 * j → g i < 2 * j
  involutive : ∀ i, i < 2 * j → g (g i) = i
  ne : ∀ i, i < 2 * j → g i ≠ i
  noncrossing : ∀ x u, u < 2 * j → x < u → u < g x → g x < g u → False

/-- The matching with partner function `g` on `[0, 2j)`. -/
def ofNaturalPartnerFunction (g : ℕ → ℕ) (hg : IsNaturalPartnerFunction j g) :
    NoncrossingMatching j :=
  ofPartner (fun v => ⟨g v, hg.lt v v.isLt⟩)
    { involutive := fun v => Fin.ext (hg.involutive v v.isLt)
      ne := fun v h => hg.ne v v.isLt (congrArg Fin.val h)
      noncrossing := fun x u h₁ h₂ h₃ => hg.noncrossing x u u.isLt h₁ h₂ h₃ }

theorem partnerIndex_ofNaturalPartnerFunction (g : ℕ → ℕ) (hg : IsNaturalPartnerFunction j g)
    {i : ℕ} (hi : i < 2 * j) :
    (ofNaturalPartnerFunction g hg).partnerIndex i = g i := by
  rw [partnerIndex_eq _ hi, ofNaturalPartnerFunction, partner_ofPartner]

/-! ## Wrap: a new outer arch around everything -/

/-- The partner function of `wrap`: `0 ↔ 2j + 1`, everything else shifted up. -/
def wrapFn (m : NoncrossingMatching j) (i : ℕ) : ℕ :=
  if i = 0 then 2 * j + 1 else if i = 2 * j + 1 then 0 else m.partnerIndex (i - 1) + 1

theorem wrapFn_zero (m : NoncrossingMatching j) : wrapFn m 0 = 2 * j + 1 := by simp [wrapFn]
theorem wrapFn_last (m : NoncrossingMatching j) : wrapFn m (2 * j + 1) = 0 := by simp [wrapFn]
theorem wrapFn_mid (m : NoncrossingMatching j) {i : ℕ} (h0 : i ≠ 0) (hl : i ≠ 2 * j + 1) :
    wrapFn m i = m.partnerIndex (i - 1) + 1 := by simp [wrapFn, h0, hl]

theorem isNaturalPartnerFunction_wrapFn (m : NoncrossingMatching j) : IsNaturalPartnerFunction
    (j + 1) (wrapFn m) := by
  constructor
  · intro i hi
    by_cases h0 : i = 0
    · subst h0; rw [wrapFn_zero]; omega
    by_cases hl : i = 2 * j + 1
    · subst hl; rw [wrapFn_last]; omega
    rw [wrapFn_mid m h0 hl]
    have := m.partnerIndex_lt (i := i - 1) (by omega); omega
  · intro i hi
    by_cases h0 : i = 0
    · subst h0; rw [wrapFn_zero, wrapFn_last]
    by_cases hl : i = 2 * j + 1
    · subst hl; rw [wrapFn_last, wrapFn_zero]
    rw [wrapFn_mid m h0 hl]
    have hp := m.partnerIndex_lt (i := i - 1) (by omega)
    rw [wrapFn_mid m (by omega) (by omega), Nat.add_sub_cancel, m.partnerIndex_partnerIndex
      (by omega)]
    omega
  · intro i hi
    by_cases h0 : i = 0
    · subst h0; rw [wrapFn_zero]; omega
    by_cases hl : i = 2 * j + 1
    · subst hl; rw [wrapFn_last]; omega
    rw [wrapFn_mid m h0 hl]
    have := m.partnerIndex_ne (i := i - 1) (by omega); omega
  · intro x u hu h₁ h₂ h₃
    have hgu : wrapFn m u < 2 * (j + 1) := by
      by_cases h0 : u = 0
      · subst h0; rw [wrapFn_zero]; omega
      by_cases hl : u = 2 * j + 1
      · subst hl; rw [wrapFn_last]; omega
      rw [wrapFn_mid m h0 hl]; have := m.partnerIndex_lt (i := u - 1) (by omega); omega
    by_cases hx0 : x = 0
    · subst hx0; rw [wrapFn_zero] at h₂ h₃; omega
    by_cases hxl : x = 2 * j + 1
    · omega
    by_cases hul : u = 2 * j + 1
    · subst hul; rw [wrapFn_last] at h₃; omega
    rw [wrapFn_mid m hx0 hxl] at h₂ h₃
    rw [wrapFn_mid m (by omega) hul] at h₃
    exact m.partnerIndex_noncrossing (x := x - 1) (u := u - 1) (by omega) (by omega) (by omega)
      (by omega)

/-- Wrap: the matching `m` inside a new outer arch `(0, 2j + 1)`. -/
def wrap (m : NoncrossingMatching j) : NoncrossingMatching (j + 1) := ofNaturalPartnerFunction
    (wrapFn m) (isNaturalPartnerFunction_wrapFn m)

theorem partnerIndex_wrap (m : NoncrossingMatching j) {i : ℕ} (hi : i < 2 * (j + 1)) :
    (wrap m).partnerIndex i = if i = 0 then 2 * j + 1 else if i = 2 * j + 1 then 0 else
      m.partnerIndex (i - 1) + 1 :=
  partnerIndex_ofNaturalPartnerFunction _ _ hi

/-! ## Rotate: point `i` becomes `i - 1`, the first point moves to the back -/

/-- The partner function of `rotate`. -/
def rotateFn (m : NoncrossingMatching j) (i : ℕ) : ℕ :=
  if i + 1 = 2 * j then m.partnerIndex 0 - 1
  else if m.partnerIndex (i + 1) = 0 then 2 * j - 1
  else m.partnerIndex (i + 1) - 1

theorem rotateFn_last (m : NoncrossingMatching j) {i : ℕ} (h : i + 1 = 2 * j) :
    rotateFn m i = m.partnerIndex 0 - 1 := by
  simp [rotateFn, h]
theorem rotateFn_zero (m : NoncrossingMatching j) {i : ℕ} (h : i + 1 ≠ 2 * j)
    (h' : m.partnerIndex (i + 1) = 0) :
    rotateFn m i = 2 * j - 1 := by simp [rotateFn, h, h']
theorem rotateFn_mid (m : NoncrossingMatching j) {i : ℕ} (h : i + 1 ≠ 2 * j)
    (h' : m.partnerIndex (i + 1) ≠ 0) :
    rotateFn m i = m.partnerIndex (i + 1) - 1 := by simp [rotateFn, h, h']

/-- `rotateFn` at a point of the boundary, with the facts each case needs. -/
theorem rotateFn_lt (m : NoncrossingMatching j) {i : ℕ} (hi : i < 2 * j) : rotateFn m i < 2 * j :=
    by
  have hp0 := m.partnerIndex_lt (i := 0) (by omega)
  by_cases hl : i + 1 = 2 * j
  · rw [rotateFn_last m hl]; omega
  by_cases hz : m.partnerIndex (i + 1) = 0
  · rw [rotateFn_zero m hl hz]; omega
  rw [rotateFn_mid m hl hz]; have := m.partnerIndex_lt (i := i + 1) (by omega); omega

theorem isNaturalPartnerFunction_rotateFn (m : NoncrossingMatching j) : IsNaturalPartnerFunction j
    (rotateFn m) := by
  constructor
  · exact fun i hi => rotateFn_lt m hi
  · intro i hi
    have hp0 := m.partnerIndex_lt (i := 0) (by omega)
    have hp0ne := m.partnerIndex_ne (i := 0) (by omega)
    have hpp0 := m.partnerIndex_partnerIndex (i := 0) (by omega)
    by_cases hl : i + 1 = 2 * j
    · rw [rotateFn_last m hl]
      rw [rotateFn_zero m (by omega)
        (by rw [show m.partnerIndex 0 - 1 + 1 = m.partnerIndex 0 by omega, hpp0])]
      omega
    by_cases hz : m.partnerIndex (i + 1) = 0
    · rw [rotateFn_zero m hl hz]
      rw [rotateFn_last m (by omega)]
      have : i + 1 = m.partnerIndex 0 := by
        have hp := m.partnerIndex_partnerIndex (i := i + 1) (by omega)
        rw [hz] at hp; exact hp.symm
      omega
    rw [rotateFn_mid m hl hz]
    have hp := m.partnerIndex_lt (i := i + 1) (by omega)
    have hpp := m.partnerIndex_partnerIndex (i := i + 1) (by omega)
    rw [rotateFn_mid m (by omega) (by
      rw [show m.partnerIndex (i + 1) - 1 + 1 = m.partnerIndex (i + 1) by omega, hpp]
      omega)]
    rw [show m.partnerIndex (i + 1) - 1 + 1 = m.partnerIndex (i + 1) by omega, hpp]
    omega
  · intro i hi
    have hp0 := m.partnerIndex_lt (i := 0) (by omega)
    by_cases hl : i + 1 = 2 * j
    · rw [rotateFn_last m hl]; omega
    by_cases hz : m.partnerIndex (i + 1) = 0
    · rw [rotateFn_zero m hl hz]; omega
    rw [rotateFn_mid m hl hz]
    have := m.partnerIndex_ne (i := i + 1) (by omega); omega
  · intro x u hu h₁ h₂ h₃
    have hgu := rotateFn_lt m hu
    have hp0 := m.partnerIndex_lt (i := 0) (by omega)
    have hp0ne := m.partnerIndex_ne (i := 0) (by omega)
    have hpp0 := m.partnerIndex_partnerIndex (i := 0) (by omega)
    have hxl : x + 1 ≠ 2 * j := by omega
    by_cases hxz : m.partnerIndex (x + 1) = 0
    · rw [rotateFn_zero m hxl hxz] at h₂ h₃; omega
    rw [rotateFn_mid m hxl hxz] at h₂ h₃
    have hpx := m.partnerIndex_lt (i := x + 1) (by omega)
    by_cases hul : u + 1 = 2 * j
    · rw [rotateFn_last m hul] at h₃; omega
    by_cases huz : m.partnerIndex (u + 1) = 0
    · rw [rotateFn_zero m hul huz] at h₃
      have : u + 1 = m.partnerIndex 0 := by
        have hp := m.partnerIndex_partnerIndex (i := u + 1) (by omega)
        rw [huz] at hp; exact hp.symm
      exact m.partnerIndex_noncrossing (x := 0) (u := x + 1) (by omega) (by omega) (by omega)
        (by omega)
    rw [rotateFn_mid m hul huz] at h₃
    exact m.partnerIndex_noncrossing (x := x + 1) (u := u + 1) (by omega) (by omega) (by omega)
      (by omega)

/-- Rotate the boundary one step: `i ↦ i - 1`, so the first point moves to the back. -/
def rotate (m : NoncrossingMatching j) : NoncrossingMatching j := ofNaturalPartnerFunction
    (rotateFn m) (isNaturalPartnerFunction_rotateFn m)

theorem partnerIndex_rotate (m : NoncrossingMatching j) {i : ℕ} (hi : i < 2 * j) :
    (rotate m).partnerIndex i =
      if i + 1 = 2 * j then m.partnerIndex 0 - 1
      else if m.partnerIndex (i + 1) = 0 then 2 * j - 1
      else m.partnerIndex (i + 1) - 1 :=
  partnerIndex_ofNaturalPartnerFunction _ _ hi

/-! ## RotateInv: point `i` becomes `i + 1`, the last point moves to the front -/

/-- The partner function of `rotateInv`. -/
def rotateInvFn (m : NoncrossingMatching j) (i : ℕ) : ℕ :=
  if i = 0 then m.partnerIndex (2 * j - 1) + 1
  else if m.partnerIndex (i - 1) + 1 = 2 * j then 0
  else m.partnerIndex (i - 1) + 1

theorem rotateInvFn_zero (m : NoncrossingMatching j) : rotateInvFn m 0 = m.partnerIndex (2 * j - 1)
    + 1 := by
  simp [rotateInvFn]
theorem rotateInvFn_last (m : NoncrossingMatching j) {i : ℕ} (h : i ≠ 0)
    (h' : m.partnerIndex (i - 1) + 1 = 2 * j) :
    rotateInvFn m i = 0 := by simp [rotateInvFn, h, h']
theorem rotateInvFn_mid (m : NoncrossingMatching j) {i : ℕ} (h : i ≠ 0)
    (h' : m.partnerIndex (i - 1) + 1 ≠ 2 * j) :
    rotateInvFn m i = m.partnerIndex (i - 1) + 1 := by simp [rotateInvFn, h, h']

theorem rotateInvFn_lt (m : NoncrossingMatching j) {i : ℕ} (hi : i < 2 * j) : rotateInvFn m i < 2 *
    j := by
  have hpl := m.partnerIndex_lt (i := 2 * j - 1) (by omega)
  have hplne := m.partnerIndex_ne (i := 2 * j - 1) (by omega)
  by_cases h0 : i = 0
  · subst h0; rw [rotateInvFn_zero]; omega
  by_cases hl : m.partnerIndex (i - 1) + 1 = 2 * j
  · rw [rotateInvFn_last m h0 hl]; omega
  rw [rotateInvFn_mid m h0 hl]; have := m.partnerIndex_lt (i := i - 1) (by omega); omega

theorem isNaturalPartnerFunction_rotateInvFn (m : NoncrossingMatching j) : IsNaturalPartnerFunction
    j (rotateInvFn m) := by
  constructor
  · exact fun i hi => rotateInvFn_lt m hi
  · intro i hi
    have hpl := m.partnerIndex_lt (i := 2 * j - 1) (by omega)
    have hplne := m.partnerIndex_ne (i := 2 * j - 1) (by omega)
    have hppl := m.partnerIndex_partnerIndex (i := 2 * j - 1) (by omega)
    by_cases h0 : i = 0
    · subst h0
      rw [rotateInvFn_zero, rotateInvFn_last m (by omega) (by rw [Nat.add_sub_cancel, hppl]; omega)]
    by_cases hl : m.partnerIndex (i - 1) + 1 = 2 * j
    · rw [rotateInvFn_last m h0 hl, rotateInvFn_zero]
      have hpp := m.partnerIndex_partnerIndex (i := i - 1) (by omega)
      have hl' : m.partnerIndex (i - 1) = 2 * j - 1 := by omega
      rw [hl'] at hpp
      omega
    rw [rotateInvFn_mid m h0 hl]
    have hp := m.partnerIndex_lt (i := i - 1) (by omega)
    have hpp := m.partnerIndex_partnerIndex (i := i - 1) (by omega)
    rw [rotateInvFn_mid m (by omega) (by rw [Nat.add_sub_cancel, hpp]; omega),
      Nat.add_sub_cancel, hpp]
    omega
  · intro i hi
    have hpl := m.partnerIndex_lt (i := 2 * j - 1) (by omega)
    by_cases h0 : i = 0
    · subst h0; rw [rotateInvFn_zero]; omega
    by_cases hl : m.partnerIndex (i - 1) + 1 = 2 * j
    · rw [rotateInvFn_last m h0 hl]; omega
    rw [rotateInvFn_mid m h0 hl]
    have := m.partnerIndex_ne (i := i - 1) (by omega); omega
  · intro x u hu h₁ h₂ h₃
    have hgu := rotateInvFn_lt m hu
    have hpl := m.partnerIndex_lt (i := 2 * j - 1) (by omega)
    have hplne := m.partnerIndex_ne (i := 2 * j - 1) (by omega)
    have hppl := m.partnerIndex_partnerIndex (i := 2 * j - 1) (by omega)
    have hu0 : u ≠ 0 := by omega
    by_cases hul : m.partnerIndex (u - 1) + 1 = 2 * j
    · rw [rotateInvFn_last m hu0 hul] at h₃; omega
    rw [rotateInvFn_mid m hu0 hul] at h₃
    have hpu := m.partnerIndex_lt (i := u - 1) (by omega)
    by_cases hx0 : x = 0
    · subst hx0
      rw [rotateInvFn_zero] at h₂ h₃
      -- arcs `(u - 1, partnerIndex (u - 1))` and `(partnerIndex (2j - 1), 2j - 1)` interleave
      exact m.partnerIndex_noncrossing (x := u - 1) (u := m.partnerIndex (2 * j - 1)) (by omega)
        (by omega) (by omega)
        (by rw [hppl]; omega)
    by_cases hxl : m.partnerIndex (x - 1) + 1 = 2 * j
    · rw [rotateInvFn_last m hx0 hxl] at h₂; omega
    rw [rotateInvFn_mid m hx0 hxl] at h₂ h₃
    exact m.partnerIndex_noncrossing (x := x - 1) (u := u - 1) (by omega) (by omega) (by omega)
      (by omega)

/-- Rotate the boundary one step the other way: `i ↦ i + 1`, so the last point
moves to the front. -/
def rotateInv (m : NoncrossingMatching j) : NoncrossingMatching j := ofNaturalPartnerFunction
    (rotateInvFn m) (isNaturalPartnerFunction_rotateInvFn m)

theorem partnerIndex_rotateInv (m : NoncrossingMatching j) {i : ℕ} (hi : i < 2 * j) :
    (rotateInv m).partnerIndex i =
      if i = 0 then m.partnerIndex (2 * j - 1) + 1
      else if m.partnerIndex (i - 1) + 1 = 2 * j then 0
      else m.partnerIndex (i - 1) + 1 :=
  partnerIndex_ofNaturalPartnerFunction _ _ hi

/-! ## Contract: remove points `0` and `1`, join their partners, shift down by two -/

/-- The partner function of `contract`. -/
def contractFn (m : NoncrossingMatching (j + 1)) (i : ℕ) : ℕ :=
  if i + 2 = m.partnerIndex 0 then m.partnerIndex 1 - 2
  else if i + 2 = m.partnerIndex 1 then m.partnerIndex 0 - 2
  else m.partnerIndex (i + 2) - 2

theorem contractFn_p0 (m : NoncrossingMatching (j + 1)) {i : ℕ} (h : i + 2 = m.partnerIndex 0) :
    contractFn m i = m.partnerIndex 1 - 2 := by rw [contractFn, ite_eq_left h]
theorem contractFn_p1 (m : NoncrossingMatching (j + 1)) {i : ℕ} (h : i + 2 ≠ m.partnerIndex 0)
    (h' : i + 2 = m.partnerIndex 1) :
    contractFn m i = m.partnerIndex 0 - 2 := by rw [contractFn, ite_eq_right h, ite_eq_left h']
theorem contractFn_mid (m : NoncrossingMatching (j + 1)) {i : ℕ} (h : i + 2 ≠ m.partnerIndex 0)
    (h' : i + 2 ≠ m.partnerIndex 1) :
    contractFn m i = m.partnerIndex (i + 2) - 2 := by rw
      [contractFn, ite_eq_right h, ite_eq_right h']

section Contract

variable (m : NoncrossingMatching (j + 1)) (hne : m.partnerIndex 0 ≠ 1)
include hne

theorem contract_facts : 2 ≤ m.partnerIndex 0 ∧ 2 ≤ m.partnerIndex 1 ∧ m.partnerIndex 0 ≠
    m.partnerIndex 1 ∧
    m.partnerIndex 0 < 2 * (j + 1) ∧ m.partnerIndex 1 < 2 * (j + 1) := by
  have h0 := m.partnerIndex_lt (i := 0) (by omega)
  have h1 := m.partnerIndex_lt (i := 1) (by omega)
  have h0ne := m.partnerIndex_ne (i := 0) (by omega)
  have h1ne := m.partnerIndex_ne (i := 1) (by omega)
  have hpp0 := m.partnerIndex_partnerIndex (i := 0) (by omega)
  refine ⟨?_, ?_, fun h => by have := m.partnerIndex_injective (by omega) (by omega) h; omega, h0,
    h1⟩
  · omega
  · by_contra hc
    have : m.partnerIndex 1 = 0 := by omega
    rw [← this, m.partnerIndex_partnerIndex (by omega)] at hne
    exact hne rfl

omit hne in
/-- For `i < 2j` not hitting the two special cases, `partnerIndex (i + 2)` is
neither `0` nor `1`. -/
theorem contract_mid_facts {i : ℕ} (hi : i < 2 * j) (h : i + 2 ≠ m.partnerIndex 0)
    (h' : i + 2 ≠ m.partnerIndex 1) :
    2 ≤ m.partnerIndex (i + 2) ∧ m.partnerIndex (i + 2) < 2 * (j + 1) := by
  have hlt := m.partnerIndex_lt (i := i + 2) (by omega)
  refine ⟨?_, hlt⟩
  by_contra hc
  have hpp := m.partnerIndex_partnerIndex (i := i + 2) (by omega)
  rcases Nat.lt_or_ge (m.partnerIndex (i + 2)) 1 with h0 | h1
  · have : m.partnerIndex (i + 2) = 0 := by omega
    rw [this] at hpp; exact h hpp.symm
  · have : m.partnerIndex (i + 2) = 1 := by omega
    rw [this] at hpp; exact h' hpp.symm

theorem contractFn_lt {i : ℕ} (hi : i < 2 * j) : contractFn m i < 2 * j := by
  obtain ⟨h0, h1, hne', hl0, hl1⟩ := contract_facts m hne
  by_cases c0 : i + 2 = m.partnerIndex 0
  · rw [contractFn_p0 m c0]; omega
  by_cases c1 : i + 2 = m.partnerIndex 1
  · rw [contractFn_p1 m c0 c1]; omega
  rw [contractFn_mid m c0 c1]
  have := contract_mid_facts m hi c0 c1; omega

theorem isNaturalPartnerFunction_contractFn : IsNaturalPartnerFunction j (contractFn m) := by
  obtain ⟨h0, h1, hne', hl0, hl1⟩ := contract_facts m hne
  have hpp0 := m.partnerIndex_partnerIndex (i := 0) (by omega)
  have hpp1 := m.partnerIndex_partnerIndex (i := 1) (by omega)
  constructor
  · exact fun i hi => contractFn_lt m hne hi
  · intro i hi
    by_cases c0 : i + 2 = m.partnerIndex 0
    · rw [contractFn_p0 m c0, contractFn_p1 m (by omega) (by omega)]; omega
    by_cases c1 : i + 2 = m.partnerIndex 1
    · rw [contractFn_p1 m c0 c1, contractFn_p0 m (by omega)]; omega
    rw [contractFn_mid m c0 c1]
    obtain ⟨hm2, hml⟩ := contract_mid_facts m hi c0 c1
    have hpp := m.partnerIndex_partnerIndex (i := i + 2) (by omega)
    have hq0 : m.partnerIndex (i + 2) - 2 + 2 ≠ m.partnerIndex 0 := fun h => by
      rw [show m.partnerIndex (i + 2) - 2 + 2 = m.partnerIndex (i + 2) by omega] at h
      have := m.partnerIndex_injective (by omega) (by omega) h; omega
    have hq1 : m.partnerIndex (i + 2) - 2 + 2 ≠ m.partnerIndex 1 := fun h => by
      rw [show m.partnerIndex (i + 2) - 2 + 2 = m.partnerIndex (i + 2) by omega] at h
      have := m.partnerIndex_injective (by omega) (by omega) h; omega
    rw [contractFn_mid m hq0 hq1, show m.partnerIndex (i + 2) - 2 + 2 = m.partnerIndex (i + 2) by
      omega, hpp]
    omega
  · intro i hi
    by_cases c0 : i + 2 = m.partnerIndex 0
    · rw [contractFn_p0 m c0]; omega
    by_cases c1 : i + 2 = m.partnerIndex 1
    · rw [contractFn_p1 m c0 c1]; omega
    rw [contractFn_mid m c0 c1]
    have := contract_mid_facts m hi c0 c1
    have := m.partnerIndex_ne (i := i + 2) (by omega); omega
  · intro x u hu h₁ h₂ h₃
    have hgu := contractFn_lt m hne hu
    by_cases x0 : x + 2 = m.partnerIndex 0
    · rw [contractFn_p0 m x0] at h₂ h₃
      by_cases u0 : u + 2 = m.partnerIndex 0
      · omega
      by_cases u1 : u + 2 = m.partnerIndex 1
      · rw [contractFn_p1 m u0 u1] at h₃; omega
      rw [contractFn_mid m u0 u1] at h₃
      have := contract_mid_facts m hu u0 u1
      exact m.partnerIndex_noncrossing (x := 1) (u := u + 2) (by omega) (by omega) (by omega)
        (by omega)
    by_cases x1 : x + 2 = m.partnerIndex 1
    · rw [contractFn_p1 m x0 x1] at h₂ h₃
      by_cases u0 : u + 2 = m.partnerIndex 0
      · omega
      by_cases u1 : u + 2 = m.partnerIndex 1
      · omega
      rw [contractFn_mid m u0 u1] at h₃
      have := contract_mid_facts m hu u0 u1
      exact m.partnerIndex_noncrossing (x := 0) (u := u + 2) (by omega) (by omega) (by omega)
        (by omega)
    rw [contractFn_mid m x0 x1] at h₂ h₃
    have hx := contract_mid_facts m (by omega) x0 x1
    by_cases u0 : u + 2 = m.partnerIndex 0
    · rw [contractFn_p0 m u0] at h₃
      exact m.partnerIndex_noncrossing (x := 0) (u := x + 2) (by omega) (by omega) (by omega)
        (by omega)
    by_cases u1 : u + 2 = m.partnerIndex 1
    · rw [contractFn_p1 m u0 u1] at h₃
      exact m.partnerIndex_noncrossing (x := 1) (u := x + 2) (by omega) (by omega) (by omega)
        (by omega)
    rw [contractFn_mid m u0 u1] at h₃
    have hu' := contract_mid_facts m hu u0 u1
    exact m.partnerIndex_noncrossing (x := x + 2) (u := u + 2) (by omega) (by omega) (by omega)
      (by omega)

/-- Contract the first two points, which must not be partners: their partners become
partners, and everything shifts down by two. -/
def contract : NoncrossingMatching j := ofNaturalPartnerFunction (contractFn m)
    (isNaturalPartnerFunction_contractFn m hne)

theorem partnerIndex_contract {i : ℕ} (hi : i < 2 * j) :
    (contract m hne).partnerIndex i =
      if i + 2 = m.partnerIndex 0 then m.partnerIndex 1 - 2
      else if i + 2 = m.partnerIndex 1 then m.partnerIndex 0 - 2
      else m.partnerIndex (i + 2) - 2 :=
  partnerIndex_ofNaturalPartnerFunction _ _ hi

end Contract

/-! ## DropOuter: remove the outer arch `(0, 2j + 1)`, shift down by one -/

/-- The partner function of `dropOuter`. -/
def dropOuterFn (m : NoncrossingMatching (j + 1)) (i : ℕ) : ℕ := m.partnerIndex (i + 1) - 1

section DropOuter

variable (m : NoncrossingMatching (j + 1)) (h : m.partnerIndex 0 = 2 * j + 1)
include h

theorem dropOuter_facts {i : ℕ} (hi : i < 2 * j) :
    1 ≤ m.partnerIndex (i + 1) ∧ m.partnerIndex (i + 1) ≤ 2 * j := by
  have hlt := m.partnerIndex_lt (i := i + 1) (by omega)
  have hpp := m.partnerIndex_partnerIndex (i := i + 1) (by omega)
  have hpp0 := m.partnerIndex_partnerIndex (i := 0) (by omega)
  constructor
  · by_contra hc
    have : m.partnerIndex (i + 1) = 0 := by omega
    rw [this, h] at hpp; omega
  · by_contra hc
    have : m.partnerIndex (i + 1) = 2 * j + 1 := by omega
    rw [this, ← h, hpp0] at hpp; omega

theorem isNaturalPartnerFunction_dropOuterFn : IsNaturalPartnerFunction j (dropOuterFn m) := by
  constructor
  · intro i hi
    have := dropOuter_facts m h hi
    unfold dropOuterFn; omega
  · intro i hi
    have hf := dropOuter_facts m h hi
    have hpp := m.partnerIndex_partnerIndex (i := i + 1) (by omega)
    unfold dropOuterFn
    rw [show m.partnerIndex (i + 1) - 1 + 1 = m.partnerIndex (i + 1) by omega, hpp]; omega
  · intro i hi
    have hf := dropOuter_facts m h hi
    have := m.partnerIndex_ne (i := i + 1) (by omega)
    unfold dropOuterFn; omega
  · intro x u hu h₁ h₂ h₃
    have hfx := dropOuter_facts m h (i := x) (by omega)
    have hfu := dropOuter_facts m h hu
    unfold dropOuterFn at h₂ h₃
    exact m.partnerIndex_noncrossing (x := x + 1) (u := u + 1) (by omega) (by omega) (by omega)
      (by omega)

/-- Drop the outer arch `(0, 2j + 1)` and shift everything down by one. -/
def dropOuter : NoncrossingMatching j := ofNaturalPartnerFunction (dropOuterFn m)
    (isNaturalPartnerFunction_dropOuterFn m h)

theorem partnerIndex_dropOuter {i : ℕ} (hi : i < 2 * j) : (dropOuter m h).partnerIndex i =
    m.partnerIndex (i + 1) - 1 :=
  partnerIndex_ofNaturalPartnerFunction _ _ hi

end DropOuter

/-! ## The cap at the gate: `contract ∘ rotateInv` -/

section Cap

variable (m : NoncrossingMatching (j + 1)) (h : m.partnerIndex 0 ≠ 2 * j + 1)
include h

end Cap

end NoncrossingMatching

end Meanders
