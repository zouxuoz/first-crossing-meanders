import Meanders.Models.FirstCrossing.Native.State
import Meanders.Models.FirstCrossing.Original.Schedule

/-!
# Retained First-Crossing port bounds

The original counter feasibility checks and the prescribed asymmetric schedule
bound the reconstructed geometry before the native key-size guard is consulted.
LOW uses its chronological first-height filter. HIGH combines the initial skirt,
central alternating pairs, and final skirt with the forced-FIFO port formula.
-/

namespace Meanders.FirstCrossing

/-- One owner's two retained groups after forced FIFO draining. -/
def ownerPorts (i j A B c e : ℕ) : ℕ :=
  let h := i - 2 * c
  let k := j - 2 * e
  let E := h - (A - c)
  let F := k - (B - e)
  (h - E + (E - F)) + (k - F + (F - E))

/-- Retention never creates ports beyond the original active endpoints. -/
theorem ownerPorts_le_visits (i j A B c e : ℕ) : ownerPorts i j A B c e ≤ i + j := by
  dsimp only [ownerPorts]
  omega

/-- At central stages the budget-adjusted progresses differ by at most one. -/
theorem ownerPorts_le_budget_succ {i j A B c e : ℕ}
    (hc : 2 * c ≤ i) (he : 2 * e ≤ j) (hcA : c ≤ A) (heB : e ≤ B)
    (hij : i + B ≤ j + A + 1) (hji : j + A ≤ i + B + 1) :
    ownerPorts i j A B c e ≤ A + B + 1 := by
  dsimp only [ownerPorts]
  omega

/-- Once one side finishes, each retained owner port is bounded by unread vertices. -/
theorem ownerPorts_le_unread {i j L R A B c e w : ℕ}
    (hL : L = 2 * A + w) (hR : R = 2 * B + w)
    (hi : i ≤ L) (hj : j ≤ R) (hc : 2 * c ≤ i) (he : 2 * e ≤ j)
    (hcA : c ≤ A) (heB : e ≤ B)
    (hfeas : A - c ≤ L - i) (hgfeas : B - e ≤ R - j)
    (hfinish : i = L ∨ j = R) :
    ownerPorts i j A B c e ≤ (L - i) + (R - j) := by
  dsimp only [ownerPorts]
  rcases hfinish with hfinish | hfinish <;> omega

/-- A prefix of alternating pairs has at most one extra long-side visit. -/
theorem alternating_prefix_counts (long short : Side) (hne : long ≠ short)
    (m tick : ℕ) :
    let xs := ((List.replicate m [long, short]).flatten).take tick
    xs.count short ≤ xs.count long ∧ xs.count long ≤ xs.count short + 1 := by
  induction m generalizing tick with
  | zero => simp
  | succ m ih =>
    cases tick with
    | zero => simp
    | succ tick =>
      cases tick with
      | zero => simp [List.replicate_succ, hne]
      | succ tick =>
        simpa [List.replicate_succ, hne, Ne.symm hne] using ih tick

/-- The actual skew schedule has an initial skirt, central pairs, and a final skirt. -/
theorem schedule_prefix_zones (long short : Side) (hne : long ≠ short)
    (delta m tick : ℕ) :
    let xs := (List.replicate delta long ++
      (List.replicate m [long, short]).flatten ++ List.replicate delta long).take tick
    let l := xs.count long
    let r := xs.count short
    (l ≤ delta ∧ r = 0) ∨ (delta + r ≤ l ∧ l ≤ delta + r + 1) ∨
      (r = m ∧ m + delta ≤ l ∧ l ≤ m + 2 * delta) := by
  dsimp only
  by_cases hfirst : tick ≤ delta
  · left
    simp [List.take_append, List.take_replicate,
      List.length_replicate, Nat.sub_eq_zero_of_le hfirst, List.count_replicate, hne]
  · by_cases hcentral : tick ≤ delta + 2 * m
    · right; left
      have ha := alternating_prefix_counts long short hne m (tick - delta)
      have hz : tick - (delta + 2 * m) = 0 := by omega
      simp only [List.take_append, List.length_append, List.length_replicate,
        length_alternating, hz, List.take_replicate,
        List.count_append]
      simp only [List.count_replicate]
      simp [hne]
      omega
    · right; right
      have ht : 2 * m ≤ tick - delta := by omega
      have he : ((List.replicate m [long, short]).flatten).take (tick - delta) =
          (List.replicate m [long, short]).flatten :=
        List.take_of_length_le (by simpa only [length_alternating] using ht)
      simp only [List.take_append, List.length_append, List.length_replicate,
        length_alternating, List.take_replicate, he, List.count_append]
      simp only [List.count_replicate, count_alternating]
      simp [hne]
      omega

/-- The two owner bounds combine uniformly over all three schedule zones. -/
theorem high_ports_of_zones {i j m delta d A B C D c e f g u v : ℕ}
    (hdelta : delta ≤ d)
    (hA : m + 2 * delta = 2 * A + u) (hB : m = 2 * B + u)
    (hC : m + 2 * delta = 2 * C + v) (hD : m = 2 * D + v)
    (hbudget : A + B + C + D = 2 * d)
    (hi : i ≤ m + 2 * delta) (hj : j ≤ m)
    (hc : 2 * c ≤ i) (he : 2 * e ≤ j) (hf : 2 * f ≤ i) (hg : 2 * g ≤ j)
    (hcA : c ≤ A) (heB : e ≤ B) (hfC : f ≤ C) (hgD : g ≤ D)
    (hcf : A - c ≤ m + 2 * delta - i) (hef : B - e ≤ m - j)
    (hff : C - f ≤ m + 2 * delta - i) (hgf : D - g ≤ m - j)
    (hzones : (i ≤ delta ∧ j = 0) ∨ (delta + j ≤ i ∧ i ≤ delta + j + 1) ∨
      (j = m ∧ m + delta ≤ i ∧ i ≤ m + 2 * delta)) :
    ownerPorts i j A B c e + ownerPorts i j C D f g ≤ 2 * d + 2 := by
  rcases hzones with hz | hz | hz
  · have hp := ownerPorts_le_visits i j A B c e
    have hq := ownerPorts_le_visits i j C D f g
    omega
  · have hp := ownerPorts_le_budget_succ hc he hcA heB (by omega) (by omega)
    have hq := ownerPorts_le_budget_succ hf hg hfC hgD (by omega) (by omega)
    omega
  · have hp := ownerPorts_le_unread hA hB hi hj hc he hcA heB hcf hef (Or.inr hz.1)
    have hq := ownerPorts_le_unread hC hD hi hj hf hg hfC hgD hff hgf (Or.inr hz.1)
    omega

/-- Port count in the native storage order. -/
def Geometry.ports (g : Geometry) : ℕ :=
  g.length.pl + g.length.pr + g.length.ql + g.length.qr

/-- LOW's original-height filter alone bounds the retained geometry. -/
theorem low_geometry_port_bound (n K : ℕ) (t : Stage) (c : Counters)
    (hc : countersValid ⟨n, K, .low⟩ t c = true)
    (hp : prefixAllowed ⟨n, K, .low⟩ t c = true) :
    (geometry ⟨n, K, .low⟩ t c).ports ≤ 2 * (K - 1) := by
  simp [countersValid, Group.all, Group.side, Counters.get, Stage.processed,
    RunSpec.sideLength, RunSpec.budgets, Sector.budgets, Counters.ofTuple] at hc
  simp [prefixAllowed] at hp
  dsimp [geometry, Geometry.ports, Counters.ofFn, Counters.get, Group.side, Stage.processed]
  omega

/-- Exchanging the two half-storage groups preserves the owner port total. -/
theorem ownerPorts_comm (i j A B c e : ℕ) :
    ownerPorts i j A B c e = ownerPorts j i B A e c := by
  dsimp only [ownerPorts]
  omega

/-- Native reconstructed geometry is the sum of the two owner port formulas. -/
theorem geometry_high_ports (n K L u v : ℕ) (t : Stage) (c : Counters) :
    (geometry ⟨n, K, .high L u v⟩ t c).ports =
      ownerPorts t.left t.right ((L - u) / 2) ((2 * n - L - u) / 2) c.pl c.pr +
      ownerPorts t.left t.right ((L - v) / 2) ((2 * n - L - v) / 2) c.ql c.qr := by
  simp only [geometry, Geometry.ports, Counters.ofFn, Counters.get, Group.side,
    Group.other, Stage.processed, RunSpec.budgets, Sector.budgets, Counters.ofTuple,
    ownerPorts, Nat.add_assoc]

set_option maxHeartbeats 2000000 in
-- Budget division and counter feasibility generate many Presburger arithmetic cases.
/-- HIGH's actual schedule and feasible original counters imply its retained-port guard. -/
theorem high_geometry_port_bound {n K L u v : ℕ} (ha : Admissible n K L u v)
    (hK : K ≤ n) (tick : ℕ) (c : Counters)
    (hc : countersValid ⟨n, K, .high L u v⟩
      (Stage.ofTick ⟨n, K, .high L u v⟩ tick) c = true) :
    (geometry ⟨n, K, .high L u v⟩ (Stage.ofTick ⟨n, K, .high L u v⟩ tick) c).ports ≤
      2 * (n - K) + 2 := by
  let t := Stage.ofTick ⟨n, K, .high L u v⟩ tick
  change countersValid ⟨n, K, .high L u v⟩ t c = true at hc
  change (geometry ⟨n, K, .high L u v⟩ t c).ports ≤ _
  simp only [countersValid, Group.all, Stage.processed, Group.side, RunSpec.sideLength,
    Counters.get, RunSpec.budgets, Counters.ofTuple, Sector.budgets, tsub_le_iff_right,
    Bool.decide_and, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  obtain ⟨hpl, hpr, hql, hqr⟩ := hc
  rcases ha with ⟨hL, hu, hv, hup, hvp, huv⟩
  have huL : u ≤ L := le_trans hu (min_le_left _ _)
  have huR : u ≤ 2 * n - L := le_trans hu (min_le_right _ _)
  have hvL : v ≤ L := le_trans hv (min_le_left _ _)
  have hvR : v ≤ 2 * n - L := le_trans hv (min_le_right _ _)
  by_cases hlong : n ≤ L
  · have hd : (if L ≤ n then n - L else L - n) = L - n := by split <;> omega
    have hm : n - (L - n) = 2 * n - L := by omega
    have hs := schedule_prefix_zones .left .right (by decide) (L - n) (2 * n - L) tick
    have ht : (t.left ≤ L - n ∧ t.right = 0) ∨
        (L - n + t.right ≤ t.left ∧ t.left ≤ L - n + t.right + 1) ∨
        (t.right = 2 * n - L ∧ (2 * n - L) + (L - n) ≤ t.left ∧
          t.left ≤ (2 * n - L) + 2 * (L - n)) := by
      simpa only [t, Stage.ofTick, RunSpec.schedule, Sector.schedule,
        ite_eq_right (by omega : ¬ L < n), hd, hm] using hs
    have hr := high_ports_of_zones
      (i := t.left) (j := t.right) (m := 2 * n - L) (delta := L - n) (d := n - K)
      (A := (L - u) / 2) (B := (2 * n - L - u) / 2) (C := (L - v) / 2) (D := (2 * n - L - v) / 2)
      (c := c.pl) (e := c.pr) (f := c.ql) (g := c.qr) (u := u) (v := v)
      (by clear hpl hpr hql hqr ht; omega) (by clear hpl hpr hql hqr ht; omega)
      (by clear hpl hpr hql hqr ht; omega) (by clear hpl hpr hql hqr ht; omega)
      (by clear hpl hpr hql hqr ht; omega) (by clear hpl hpr hql hqr ht; omega)
      (by omega) hpr.1 hpl.2.1 hpr.2.1 hql.2.1 hqr.2.1
      hpl.2.2.1 hpr.2.2.1 hql.2.2.1 hqr.2.2.1
      (by omega) (by omega) (by omega) (by omega) ht
    rw [geometry_high_ports]
    exact hr
  · have hnL : L ≤ n := by omega
    have hd : (if L ≤ n then n - L else L - n) = n - L := by simp [hnL]
    have hm : n - (n - L) = L := by omega
    have hs := schedule_prefix_zones .right .left (by decide) (n - L) L tick
    have ht : (t.right ≤ n - L ∧ t.left = 0) ∨
        (n - L + t.left ≤ t.right ∧ t.right ≤ n - L + t.left + 1) ∨
        (t.left = L ∧ L + (n - L) ≤ t.right ∧ t.right ≤ L + 2 * (n - L)) := by
      simpa only [t, Stage.ofTick, RunSpec.schedule, Sector.schedule,
        ite_eq_left (by omega : L < n), hd, hm] using hs
    have hr := high_ports_of_zones
      (i := t.right) (j := t.left) (m := L) (delta := n - L) (d := n - K)
      (A := (2 * n - L - u) / 2) (B := (L - u) / 2) (C := (2 * n - L - v) / 2) (D := (L - v) / 2)
      (c := c.pr) (e := c.pl) (f := c.qr) (g := c.ql) (u := u) (v := v)
      (by clear hpl hpr hql hqr ht; omega) (by clear hpl hpr hql hqr ht; omega)
      (by clear hpl hpr hql hqr ht; omega) (by clear hpl hpr hql hqr ht; omega)
      (by clear hpl hpr hql hqr ht; omega) (by clear hpl hpr hql hqr ht; omega)
      (by omega) hpl.1 hpr.2.1 hpl.2.1 hqr.2.1 hql.2.1
      hpr.2.2.1 hpl.2.2.1 hqr.2.2.1 hql.2.2.1
      (by omega) (by omega) (by omega) (by omega) ht
    rw [geometry_high_ports, ownerPorts_comm t.left t.right ((L - u) / 2),
      ownerPorts_comm t.left t.right ((L - v) / 2)]
    exact hr

/-- The native retained-port test follows from independent stage/counter/source checks. -/
theorem geometry_port_bound (s : RunSpec) (t : Stage) (c : Counters)
    (hs : s.valid = true) (ht : t.valid s = true)
    (hc : countersValid s t c = true) (hp : prefixAllowed s t c = true) :
    (geometry s t c).ports ≤ s.portBound := by
  have htt : t = Stage.ofTick s t.tick := (of_decide_eq_true ht).2
  cases s with
  | mk n K sector =>
    cases sector with
    | low => exact low_geometry_port_bound n K t c hc hp
    | high L u v =>
      simp only [RunSpec.valid, Bool.and_eq_true, decide_eq_true_eq] at hs
      have hmeta := hs.1
      have ha := hs.2.2.2
      rw [htt] at hc ⊢
      exact high_geometry_port_bound ha hmeta.2.2 t.tick c hc

/-- Flat storage has precisely the sum of the reconstructed four group lengths. -/
theorem Ports.ofLengths_flat_length (len : Counters) :
    (Ports.ofLengths len).flat.length = len.pl + len.pr + len.ql + len.qr := by
  simp [Ports.ofLengths, Ports.flat, Nat.add_assoc]

/-- A representation proof of mate coverage suffices for the executable size guard. -/
theorem mate_length_port_bound (s : RunSpec) (t : Stage) (x : Key)
    (hs : s.valid = true) (ht : t.valid s = true)
    (hc : countersValid s t x.counters = true) (hp : prefixAllowed s t x.counters = true)
    (hcover : x.mate.length = (Ports.ofLengths (geometry s t x.counters).length).flat.length) :
    x.mate.length ≤ s.portBound := by
  rw [hcover, Ports.ofLengths_flat_length]
  exact geometry_port_bound s t x.counters hs ht hc hp

end Meanders.FirstCrossing
