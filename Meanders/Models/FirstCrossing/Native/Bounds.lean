import Meanders.Models.FirstCrossing.Native.Codec
import Meanders.Models.FirstCrossing.Native.PortBound
import Mathlib.Data.Fintype.Card

/-!
# Finite native First-Crossing carrier bounds

The canonical decoder injects validated raw keys into four bounded original
counters and a bounded-rank noncrossing matching. These finite cardinality
bounds implement the fixed BASE2 carrier envelope. They do not assert a time,
space, arithmetic bit-cost, source-history, or evaluator-correctness theorem.
-/

namespace Meanders.FirstCrossing

private theorem orderFromList_heq {n m size size' : Nat} {xs ys : List Nat}
    (hp : xs.Perm (List.range size)) (hq : ys.Perm (List.range size'))
    (hn : xs.length = 2 * n) (hm : ys.length = 2 * m)
    (hxs : xs = ys) (hsize : size = size') (hr : n = m) :
    HEq (orderFromList xs hp hn) (orderFromList ys hq hm) := by
  subst ys
  subst size'
  subst m
  rfl

/-- Equal original counters and equal mate lengths fix the cyclic relabelling. -/
theorem keyOrder_heq {s : RunSpec} {t : Stage} {x y : Key}
    (hx : validKey s t x = true) (hy : validKey s t y = true)
    (hc : x.counters = y.counters) (hl : x.mate.length = y.mate.length) :
    HEq (keyOrder s t x hx) (keyOrder s t y hy) := by
  unfold keyOrder portsOrder
  apply orderFromList_heq
  · rw [hc]
  · exact hl
  · omega

/-- Original counters plus the canonical decoded matching determine every raw key byte. -/
theorem key_eq_of_decode {s : RunSpec} {t : Stage} {x y : Key}
    (hx : validKey s t x = true) (hy : validKey s t y = true)
    (hc : x.counters = y.counters)
    (hd : (⟨x.mate.length / 2, decodeKey s t x hx⟩ : Σ r, NoncrossingMatching r) =
      ⟨y.mate.length / 2, decodeKey s t y hy⟩) : x = y := by
  have hr : x.mate.length / 2 = y.mate.length / 2 := congrArg Sigma.fst hd
  have hl : x.mate.length = y.mate.length := by
    have hxl := validKey_twice_rank hx
    have hyl := validKey_twice_rank hy
    omega
  have hm : HEq (decodeKey s t x hx) (decodeKey s t y hy) := (Sigma.mk.inj hd).2
  have ho := keyOrder_heq hx hy hc hl
  have he : encodeMatching (decodeKey s t x hx) (keyOrder s t x hx) =
      encodeMatching (decodeKey s t y hy) (keyOrder s t y hy) := by
    congr 1
  rw [decodeKey_roundtrip, decodeKey_roundtrip] at he
  cases x
  cases y
  exact congrArg₂ Key.mk hc he

/-- Valid original down budgets never exceed the ordinary source order. -/
theorem RunSpec.budget_le_order {s : RunSpec} (hs : s.valid = true) (g : Group) :
    s.budgets.get g ≤ s.n := by
  cases s with
  | mk n K sector =>
    cases sector with
    | low => cases g <;> simp [RunSpec.budgets, Sector.budgets, Counters.ofTuple, Counters.get]
    | high L u v =>
      simp only [RunSpec.valid, Bool.and_eq_true, decide_eq_true_eq] at hs
      have hL : L < 2 * n := hs.2.2.1
      cases g <;> simp only [RunSpec.budgets, Sector.budgets, Counters.ofTuple, Counters.get] <;>
        omega

/-- Each stored coordinate is an original down counter bounded by the source order. -/
theorem validKey_counter_le {s : RunSpec} {t : Stage} {x : Key}
    (hx : validKey s t x = true) (g : Group) : x.counters.get g ≤ s.n := by
  simp only [validKey, Bool.and_eq_true, decide_eq_true_eq] at hx
  have hs : s.valid = true := hx.1.1.1.1.1.1
  have hc : countersValid s t x.counters = true := hx.1.1.1.1.2
  have hg : g ∈ Group.all := by cases g <;> simp [Group.all]
  have hb := (List.all_eq_true.mp hc) g hg
  have hcb : x.counters.get g ≤ s.budgets.get g := (of_decide_eq_true hb).2.2.1
  exact hcb.trans (RunSpec.budget_le_order hs g)

/-- The decoder's rank obeys the independent retained-port envelope. -/
theorem validKey_rank_le {s : RunSpec} {t : Stage} {x : Key}
    (hx : validKey s t x = true) : x.mate.length / 2 ≤ s.portBound / 2 := by
  have hcover := (validKey_pairing_contract hx).1
  simp only [validKey, Bool.and_eq_true, decide_eq_true_eq] at hx
  have hl := mate_length_port_bound s t x hx.1.1.1.1.1.1 hx.1.1.1.1.1.2
    hx.1.1.1.1.2 hx.1.1.1.2 hcover
  omega

/-- The canonical finite carrier at one fixed sector and stage. -/
def ValidCarrier (s : RunSpec) (t : Stage) := {x : Key // validKey s t x = true}

/-- Four bounded original counters and one bounded-rank noncrossing matching.
No independent port colouring or marked-subset coordinate is present. -/
abbrev CarrierCode (s : RunSpec) :=
  (Fin (s.n + 1) × Fin (s.n + 1) × Fin (s.n + 1) × Fin (s.n + 1)) ×
    (Σ r : Fin (s.portBound / 2 + 1), NoncrossingMatching r.val)

/-- Encode the concrete raw carrier through its already-proved canonical decoder. -/
noncomputable def carrierCode (s : RunSpec) (t : Stage) (x : ValidCarrier s t) : CarrierCode s :=
  (⟨⟨x.val.counters.pl, Nat.lt_succ_of_le (validKey_counter_le x.property .pl)⟩,
      ⟨x.val.counters.pr, Nat.lt_succ_of_le (validKey_counter_le x.property .pr)⟩,
      ⟨x.val.counters.ql, Nat.lt_succ_of_le (validKey_counter_le x.property .ql)⟩,
      ⟨x.val.counters.qr, Nat.lt_succ_of_le (validKey_counter_le x.property .qr)⟩⟩,
    ⟨⟨x.val.mate.length / 2, Nat.lt_succ_of_le (validKey_rank_le x.property)⟩,
      decodeKey s t x.val x.property⟩)

/-- Encoding forgets no raw key information. -/
theorem carrierCode_injective (s : RunSpec) (t : Stage) :
    Function.Injective (carrierCode s t) := by
  intro x y he
  apply Subtype.ext
  have hc := congrArg Prod.fst he
  have hpl : x.val.counters.pl = y.val.counters.pl := congrArg (fun z => z.1.val) hc
  have hpr : x.val.counters.pr = y.val.counters.pr := congrArg (fun z => z.2.1.val) hc
  have hql : x.val.counters.ql = y.val.counters.ql := congrArg (fun z => z.2.2.1.val) hc
  have hqr : x.val.counters.qr = y.val.counters.qr := congrArg (fun z => z.2.2.2.val) hc
  have hcounter : x.val.counters = y.val.counters := by
    cases hcx : x.val.counters
    cases hcy : y.val.counters
    simp_all only
  apply key_eq_of_decode x.property y.property hcounter
  exact congrArg (fun z : Σ r : Fin (s.portBound / 2 + 1), NoncrossingMatching r.val =>
    (⟨z.1.val, z.2⟩ : Σ r, NoncrossingMatching r)) (congrArg Prod.snd he)

noncomputable instance validCarrierFintype (s : RunSpec) (t : Stage) : Fintype (ValidCarrier s t) :=
  Fintype.ofInjective (carrierCode s t) (carrierCode_injective s t)

/-- Exact Catalan envelope for the actual validated native carrier. -/
theorem carrierCard_le (s : RunSpec) (t : Stage) :
    Fintype.card (ValidCarrier s t) ≤
      (s.n + 1)^4 * ∑ r : Fin (s.portBound / 2 + 1), catalan r.val := by
  have h := Fintype.card_le_of_injective (carrierCode s t) (carrierCode_injective s t)
  simpa only [CarrierCode, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma,
    card_noncrossingMatching_eq_catalan, pow_succ, pow_zero, mul_one, one_mul,
    Nat.mul_assoc] using h

/-- Existing Catalan enumeration has the standard binary-word envelope. -/
theorem catalan_le_four_pow (r : Nat) : catalan r ≤ 4^r := by
  rw [catalan_eq_centralBinom_div]
  exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow r)

/-- A uniform finite rank sum suffices for the reference carrier bound. -/
theorem sum_catalan_le (R : Nat) :
    (∑ r : Fin (R + 1), catalan r.val) ≤ (R + 1) * 4^R := by
  calc
    _ ≤ ∑ _r : Fin (R + 1), 4^R := by
      apply Finset.sum_le_sum
      intro r _
      apply (catalan_le_four_pow r.val).trans
      gcongr <;> omega
    _ = _ := by simp

/-- Polynomial counter/rank factors times the Catalan base-four envelope. -/
theorem carrierCard_le_pow (s : RunSpec) (t : Stage) :
    Fintype.card (ValidCarrier s t) ≤
      (s.n + 1)^4 * (s.portBound / 2 + 1) * 4^(s.portBound / 2) := by
  calc
    _ ≤ (s.n + 1)^4 * ∑ r : Fin (s.portBound / 2 + 1), catalan r.val := carrierCard_le s t
    _ ≤ (s.n + 1)^4 * ((s.portBound / 2 + 1) * 4^(s.portBound / 2)) :=
      Nat.mul_le_mul_left _ (sum_catalan_le _)
    _ = _ := (Nat.mul_assoc _ _ _).symm

/-- LOW uses the independently proved `2*(K-1)` retained-port envelope. -/
theorem low_carrierCard_le (n K : Nat) (hK : 1 ≤ K) (t : Stage) :
    Fintype.card (ValidCarrier ⟨n, K, .low⟩ t) ≤ (n + 1)^4 * K * 4^(K-1) := by
  have h := carrierCard_le_pow ⟨n, K, .low⟩ t
  have hk : K - 1 + 1 = K := by omega
  simpa only [RunSpec.portBound, Nat.mul_div_cancel_left _ (by decide : 0 < 2), hk] using h

/-- HIGH counters determine all four group separators, so no port-colouring
factor is introduced by the physical carrier. -/
theorem high_carrierCard_le (n K L u v : Nat) (t : Stage) :
    Fintype.card (ValidCarrier ⟨n, K, .high L u v⟩ t) ≤
      (n + 1)^4 * (n-K+2) * 4^(n-K+1) := by
  have h := carrierCard_le_pow ⟨n, K, .high L u v⟩ t
  have hr : (2 * (n-K) + 2) / 2 = n-K+1 := by omega
  simpa only [RunSpec.portBound, hr, Nat.add_assoc] using h

/-- At the prescribed threshold, the LOW exponential factor is at most `2^n`. -/
theorem default_low_exponent (n : Nat) : 4^(n/2) ≤ 2^n := by
  calc
    4^(n/2) = 2^(2 * (n/2)) := by rw [pow_mul]; rfl
    _ ≤ 2^n := by gcongr <;> omega

/-- The extra one in the HIGH retained rank costs at most one extra binary bit. -/
theorem default_high_exponent {n : Nat} (hn : 0 < n) :
    4^(n-(n/2+1)+1) ≤ 2^(n+1) := by
  calc
    _ = 2^(2 * (n-(n/2+1)+1)) := by rw [pow_mul]; rfl
    _ ≤ 2^(n+1) := by gcongr <;> omega

end Meanders.FirstCrossing
