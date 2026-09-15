import Meanders.Core.Matching.Surgery
import Meanders.Core.Graph.SupEdge

/-!
# Adjacent surgery on a cyclic port pairing

These operations put the affected adjacent seam at ports zero and one.
They reuse the existing noncrossing matching surgeries and explicitly track
cyclic reindexing. Four-group geometry and the sole-final-cycle policy belong
above this interface.
-/

namespace Meanders.FirstCrossing

open NoncrossingMatching SimpleGraph

/-- Insert a paired pair of adjacent ports before the existing port array. -/
def adjacentCup {n : Nat} (m : NoncrossingMatching n) : NoncrossingMatching (n + 1) :=
  rotateInv (wrap m)

theorem partnerIndex_adjacentCup {n : Nat} (m : NoncrossingMatching n) {i : Nat}
    (hi : i < 2 * (n + 1)) :
    (adjacentCup m).partnerIndex i =
      if i = 0 then 1 else if i = 1 then 0 else m.partnerIndex (i - 2) + 2 := by
  rw [adjacentCup, partnerIndex_rotateInv _ hi]
  by_cases h0 : i = 0
  · subst i
    simp only [ite_true]
    rw [partnerIndex_wrap _ (by omega)]
    simp [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
  rw [ite_eq_right h0, ite_eq_right h0, partnerIndex_wrap _ (by omega)]
  by_cases h1 : i = 1
  · subst i
    simp
    omega
  have hmid : i - 1 ≠ 0 := by omega
  have hlast : i - 1 ≠ 2 * n + 1 := by omega
  rw [ite_eq_right hmid, ite_eq_right hlast, ite_eq_right h1]
  have hp := m.partnerIndex_lt (i := i - 2) (by omega)
  have hi' : i - 1 - 1 = i - 2 := by omega
  rw [hi', ite_eq_right (by omega)]

private theorem rotate_outer_of_adjacent {n : Nat} (m : NoncrossingMatching (n + 1))
    (h : m.partnerIndex 0 = 1) : (rotate m).partnerIndex 0 = 2 * n + 1 := by
  have hp := m.partnerIndex_partnerIndex (i := 0) (by omega)
  rw [h] at hp
  rw [partnerIndex_rotate _ (by omega)]
  simp [hp, show 1 ≠ 2 * (n + 1) by omega]
  omega

/-- Delete the adjacent paired ports when joining them closes an existing path. -/
def dropAdjacent {n : Nat} (m : NoncrossingMatching (n + 1))
    (h : m.partnerIndex 0 = 1) : NoncrossingMatching n :=
  dropOuter (rotate m) (rotate_outer_of_adjacent m h)

theorem partnerIndex_dropAdjacent {n : Nat} (m : NoncrossingMatching (n + 1))
    (h : m.partnerIndex 0 = 1) {i : Nat} (hi : i < 2 * n) :
    (dropAdjacent m h).partnerIndex i = m.partnerIndex (i + 2) - 2 := by
  rw [dropAdjacent, partnerIndex_dropOuter _ _ hi,
    partnerIndex_rotate _ (by omega)]
  have hlast : i + 1 + 1 ≠ 2 * (n + 1) := by omega
  have hp0 : m.partnerIndex (i + 2) ≠ 0 := by
    intro hp
    have hh := m.partnerIndex_partnerIndex (i := i + 2) (by omega)
    rw [hp, h] at hh
    omega
  simp only [ite_eq_right hlast, show i + 1 + 1 = i + 2 by omega, ite_eq_right hp0]
  omega

/-- Cap the first two ports. The Boolean reports closure of one existing path;
it does not decide whether that closure is terminal and admissible. -/
def adjacentCap {n : Nat} (m : NoncrossingMatching (n + 1)) :
    Bool × NoncrossingMatching n :=
  if h : m.partnerIndex 0 = 1 then (true, dropAdjacent m h)
  else (false, contract m h)

@[simp] theorem adjacentCap_closes {n : Nat} (m : NoncrossingMatching (n + 1)) :
    (adjacentCap m).1 = true ↔ m.partnerIndex 0 = 1 := by
  unfold adjacentCap
  split <;> simp_all

/-- The same three-way rewiring formula applies whether or not a path closes. -/
theorem partnerIndex_adjacentCap {n : Nat} (m : NoncrossingMatching (n + 1))
    {i : Nat} (hi : i < 2 * n) :
    (adjacentCap m).2.partnerIndex i =
      if i + 2 = m.partnerIndex 0 then m.partnerIndex 1 - 2
      else if i + 2 = m.partnerIndex 1 then m.partnerIndex 0 - 2
      else m.partnerIndex (i + 2) - 2 := by
  unfold adjacentCap
  split
  · rename_i h
    dsimp only
    rw [partnerIndex_dropAdjacent m h hi]
    have hp := m.partnerIndex_partnerIndex (i := 0) (by omega)
    rw [h] at hp
    simp [h, hp]
  · dsimp only
    exact partnerIndex_contract _ _ hi

/-- A port pairing records exactly which boundary endpoints belong to one path.
This assumption says nothing about components without boundary endpoints. -/
def RepresentsPaths {V : Type*} {n : Nat} (G : SimpleGraph V)
    (port : Nat → V) (m : NoncrossingMatching n) : Prop :=
  ∀ i j, i < 2 * n → j < 2 * n →
    (G.Reachable (port i) (port j) ↔ i = j ∨ m.partnerIndex i = j)

/-- A fresh cup extends a represented set of paths by one independent path.
Only injectivity on the finite new boundary is required of the indexing map. -/
theorem adjacentCup_representsPaths {V : Type*} {n : Nat} {G : SimpleGraph V}
    {port : Nat → V} {m : NoncrossingMatching n}
    (hm : RepresentsPaths G (fun i => port (i + 2)) m)
    (hinj : Set.InjOn port (Set.Iio (2 * (n + 1))))
    (h0 : ∀ v, G.Reachable (port 0) v ↔ v = port 0)
    (h1 : ∀ v, G.Reachable (port 1) v ↔ v = port 1) :
    RepresentsPaths (G ⊔ edge (port 0) (port 1)) port (adjacentCup m) := by
  intro i j hi hj
  have he {a b : Nat} (ha : a < 2 * (n + 1)) (hb : b < 2 * (n + 1)) :
      port a = port b ↔ a = b := ⟨hinj ha hb, congrArg port⟩
  have hr0 (a : Nat) (ha : a < 2 * (n + 1)) :
      G.Reachable (port a) (port 0) ↔ a = 0 := by
    rw [reachable_comm, h0, he ha (by omega)]
  have hr1 (a : Nat) (ha : a < 2 * (n + 1)) :
      G.Reachable (port a) (port 1) ↔ a = 1 := by
    rw [reachable_comm, h1, he ha (by omega)]
  rw [reachable_sup_edge_isolated h0 h1, partnerIndex_adjacentCup m hi,
    he hi (by omega), he hj (by omega), he hi (by omega), he hj (by omega)]
  by_cases hi0 : i = 0
  · subst i
    rw [h0, he hj (by omega)]
    simp
    omega
  by_cases hi1 : i = 1
  · subst i
    rw [h1, he hj (by omega)]
    simp
    omega
  by_cases hj0 : j = 0
  · subst j
    rw [hr0 i hi]
    simp [hi0, hi1]
  by_cases hj1 : j = 1
  · subst j
    rw [hr1 i hi]
    simp [hi0, hi1]
  have hpi : i - 2 + 2 = i := by omega
  have hpj : j - 2 + 2 = j := by omega
  have hh := hm (i - 2) (j - 2) (by omega) (by omega)
  dsimp only at hh
  rw [hpi, hpj] at hh
  rw [hh]
  simp only [ite_eq_right hi0, ite_eq_right hi1]
  omega

/-- The cap's closure bit tests original path connectivity, independently of
whether the physical graph has a simple edge or a subdivided path. -/
theorem adjacentCap_closes_iff_reachable {V : Type*} {n : Nat} {G : SimpleGraph V}
    {port : Nat → V} {m : NoncrossingMatching (n + 1)}
    (hm : RepresentsPaths G port m) :
    (adjacentCap m).1 = true ↔ G.Reachable (port 0) (port 1) := by
  rw [adjacentCap_closes, hm 0 1 (by omega) (by omega)]
  simp

/-- Joining the adjacent endpoints and deleting them from the frontier preserves
the exact physical path relation on every surviving port, even in the closure
branch. Closed components cannot silently become paths in the remaining key. -/
theorem adjacentCap_representsPaths {V : Type*} {n : Nat} {G : SimpleGraph V}
    {port : Nat → V} {m : NoncrossingMatching (n + 1)}
    (hm : RepresentsPaths G port m) :
    RepresentsPaths (G ⊔ edge (port 0) (port 1)) (fun i => port (i + 2))
      (adjacentCap m).2 := by
  intro i j hi hj
  rw [reachable_sup_edge_iff,
    hm (i + 2) (j + 2) (by omega) (by omega),
    hm (i + 2) 0 (by omega) (by omega),
    hm 1 (j + 2) (by omega) (by omega),
    hm (i + 2) 1 (by omega) (by omega),
    hm 0 (j + 2) (by omega) (by omega), partnerIndex_adjacentCap m hi]
  have hp := m.partnerIndex_partnerIndex (i := i + 2) (by omega)
  have hp0 := m.partnerIndex_partnerIndex (i := 0) (by omega)
  have hp1 := m.partnerIndex_partnerIndex (i := 1) (by omega)
  by_cases h0 : i + 2 = m.partnerIndex 0
  · have hpi : m.partnerIndex (i + 2) = 0 := by rw [h0, hp0]
    have hn : m.partnerIndex 0 ≠ 1 := by omega
    have hf := m.contract_facts hn
    rw [ite_eq_left h0, hpi]
    omega
  · rw [ite_eq_right h0]
    by_cases h1 : i + 2 = m.partnerIndex 1
    · have hpi : m.partnerIndex (i + 2) = 1 := by rw [h1, hp1]
      have hn : m.partnerIndex 0 ≠ 1 := by
        intro h
        rw [h] at hp0
        omega
      have hf := m.contract_facts hn
      rw [ite_eq_left h1, hpi]
      omega
    · rw [ite_eq_right h1]
      have hf := m.contract_mid_facts hi h0 h1
      omega

/-- Old index of a port after rotating the first port to the end.
The map is only used on indices strictly below `size`. -/
def nextPort (size i : Nat) : Nat := if i + 1 = size then 0 else i + 1

theorem nextPort_lt {size i : Nat} (hi : i < size) : nextPort size i < size := by
  unfold nextPort
  split <;> omega

theorem nextPort_injective (size : Nat) : Function.Injective (nextPort size) := by
  intro i j he
  unfold nextPort at he
  split at he <;> split at he <;> omega

theorem iterate_nextPort_zero {size k : Nat} (hk : k < size) :
    (nextPort size)^[k] 0 = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp [nextPort, show k + 1 ≠ size by omega]

/-- Rotating `k` times brings exactly the original cyclic seam `(k,next k)`
to the adjacent working positions `(0,1)`. -/
theorem iterate_nextPort_seam {n k : Nat} (hk : k < 2 * n) :
    (nextPort (2 * n))^[k] 0 = k ∧
      (nextPort (2 * n))^[k] 1 = nextPort (2 * n) k := by
  refine ⟨iterate_nextPort_zero hk, ?_⟩
  have hz : nextPort (2 * n) 0 = 1 := by
    simp [nextPort, show 1 ≠ 2 * n by omega]
  rw [← hz, ← Function.iterate_succ_apply, Function.iterate_succ_apply',
    iterate_nextPort_zero hk]

/-- Rotation conjugates the mate array by the explicit cyclic index map. -/
theorem nextPort_partnerIndex_rotate {n : Nat} (m : NoncrossingMatching n)
    {i : Nat} (hi : i < 2 * n) :
    nextPort (2 * n) ((rotate m).partnerIndex i) =
      m.partnerIndex (nextPort (2 * n) i) := by
  rw [partnerIndex_rotate m hi]
  by_cases hl : i + 1 = 2 * n
  · rw [ite_eq_left hl]
    have hp := m.partnerIndex_lt (i := 0) (by omega)
    have hn := m.partnerIndex_ne (i := 0) (by omega)
    simp only [nextPort, ite_eq_left hl]
    split <;> omega
  · rw [ite_eq_right hl]
    have hp := m.partnerIndex_lt (i := i + 1) (by omega)
    by_cases hz : m.partnerIndex (i + 1) = 0
    · rw [ite_eq_left hz]
      simp [nextPort, hl, hz, show 2 * n - 1 + 1 = 2 * n by omega]
    · rw [ite_eq_right hz]
      simp only [nextPort, ite_eq_right hl]
      split <;> omega

/-- Cyclic reindexing preserves the physical path interpretation without
exchanging owners or quotienting states. -/
theorem rotate_representsPaths {V : Type*} {n : Nat} {G : SimpleGraph V}
    {port : Nat → V} {m : NoncrossingMatching n}
    (hm : RepresentsPaths G port m) :
    RepresentsPaths G (port ∘ nextPort (2 * n)) (rotate m) := by
  intro i j hi hj
  dsimp only [Function.comp_apply]
  rw [hm _ _ (nextPort_lt hi) (nextPort_lt hj),
    ← nextPort_partnerIndex_rotate m hi]
  simp only [(nextPort_injective (2 * n)).eq_iff]

/-- Repeated seam relocation retains an explicit index map back to the original
physical boundary. This transports every seam without identifying owners. -/
theorem iterate_rotate_representsPaths {V : Type*} {n : Nat} {G : SimpleGraph V}
    {port : Nat → V} {m : NoncrossingMatching n}
    (hm : RepresentsPaths G port m) (k : Nat) :
    RepresentsPaths G (port ∘ (nextPort (2 * n))^[k]) (rotate^[k] m) := by
  induction k with
  | zero => exact hm
  | succ k ih =>
    rw [Function.iterate_succ_apply' rotate]
    exact rotate_representsPaths ih

end Meanders.FirstCrossing
