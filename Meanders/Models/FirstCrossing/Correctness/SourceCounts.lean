import Meanders.Models.FirstCrossing.Native.Eval
import Meanders.Models.FirstCrossing.Interpretation.SourceHalves
import Meanders.Problems.Open

/-! Cardinal and exterior-weighted source partition, independently of evaluation. -/

namespace Meanders.FirstCrossing

/-- Every enumerated specification retains the requested rank and threshold. -/
theorem sectorSpecs_fields {n K : ℕ} {spec : RunSpec} (h : spec ∈ sectorSpecs n K) :
    spec.n = n ∧ spec.K = K := by
  obtain ⟨h, _⟩ := List.mem_filter.mp h
  simp only [List.mem_cons, List.mem_flatMap, List.mem_map] at h
  rcases h with rfl | ⟨L, _, u, _, rfl⟩ <;> exact ⟨rfl, rfl⟩

/-- At fixed rank and threshold, enumeration includes exactly valid metadata. -/
theorem mem_sectorSpecs_iff {n K : ℕ} {sector : Sector} :
    (⟨n, K, sector⟩ : RunSpec) ∈ sectorSpecs n K ↔
      (⟨n, K, sector⟩ : RunSpec).valid = true := by
  constructor
  · exact sectorSpecs_valid
  · intro hv
    apply List.mem_filter.mpr
    refine ⟨?_, hv⟩
    cases sector with
    | low => exact List.mem_cons_self
    | high L u v =>
      have hh : 0 < L ∧ L < 2 * n ∧ Admissible n K L u v := by
        simp only [RunSpec.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
        exact hv.2
      have huv := hh.2.2.2.2.2.2.2
      have hu := hh.2.2.2.1
      have hvEq : v = 2 * K - u := by omega
      subst v
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨L, List.mem_range.mpr hh.2.1, List.mem_map.mpr ?_⟩
      exact ⟨u, List.mem_range.mpr (by omega), rfl⟩

/-- The LOW-first enumeration never repeats an oriented source sector. -/
theorem sectorSpecs_nodup (n K : ℕ) : (sectorSpecs n K).Nodup := by
  apply List.Nodup.filter
  apply List.nodup_cons.mpr
  constructor
  · simp only [List.mem_flatMap, List.mem_map]
    rintro ⟨L, _, u, _, he⟩
    cases he
  · rw [List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
    constructor
    · intro L hL
      apply List.Nodup.map
      · intro u v he
        exact congrArg (fun s => match s.sector with | .low => 0 | .high _ u _ => u) he
      · exact List.nodup_range
    · apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij a ha b hb he
      obtain ⟨u, _, hua⟩ := List.mem_map.mp ha
      obtain ⟨v, _, hvb⟩ := List.mem_map.mp hb
      have hL := congrArg (fun s => match s.sector with | .low => 0 | .high L _ _ => L)
        (hua.trans (he.trans hvb.symm))
      simp only [List.getElem_range] at hL
      omega

/-- Every physical pair's actual sector passes native metadata validation. -/
theorem inSector_spec_valid {n K : ℕ} (hn : 0 < n) (hK : 0 < K) (hKn : K ≤ n)
    {P Q : NoncrossingMatching n} {sector : Sector} (hs : InSector K P Q sector) :
    (⟨n, K, sector⟩ : RunSpec).valid = true := by
  cases sector with
  | low => simp [RunSpec.valid, hn, hKn, show 1 ≤ K by omega]
  | high L u v =>
    have hint := firstHit_interior hK hs.1
    have hadm := inSector_high_admissible hs
    simp [RunSpec.valid, hn, hKn, hint, hadm, show 1 ≤ K by omega]

/-- All physical sources occur in an enumerated sector, including disconnected ones. -/
theorem exists_enumerated_sector {n K : ℕ} (hn : 0 < n) (hK : 0 < K) (hKn : K ≤ n)
    (P Q : NoncrossingMatching n) :
    ∃ sector, (⟨n, K, sector⟩ : RunSpec) ∈ sectorSpecs n K ∧ InSector K P Q sector := by
  obtain ⟨sector, hs, _⟩ := firstHeightPartition K hK P Q
  exact ⟨sector, mem_sectorSpecs_iff.mpr (inSector_spec_valid hn hK hKn hs), hs⟩

/-- Independent source reconstruction agrees with the finite sector equivalence. -/
theorem sourceEquiv_matchings (spec : RunSpec) (s : Source spec) :
    ((sourceEquiv spec) s).val = s.matchings := by
  cases spec with
  | mk n K sector => cases sector <;> rfl

/-- Source finiteness is transported from the existing finite matching-pair sector. -/
noncomputable instance sourceFintype (spec : RunSpec) : Fintype (Source spec) :=
  Fintype.ofEquiv _ (sourceEquiv spec).symm

/-- Connected original source objects in one oriented sector. -/
abbrev ConnectedSource (spec : RunSpec) :=
  {s : Source spec // (unionGraph s.matchings).Connected}

/-- Restrict the finite source language to its original connected diagrams. -/
noncomputable instance connectedSourceFintype (spec : RunSpec) :
    Fintype (ConnectedSource spec) := by
  classical
  exact Subtype.fintype _

/-- The finite set of exactly the sectors in the evaluator's canonical enumeration. -/
def enumeratedSectors (n K : ℕ) : Finset Sector :=
  ((sectorSpecs n K).map RunSpec.sector).toFinset

/-- Taking sector names retains exactly the original specification membership. -/
theorem mem_enumeratedSectors {n K : ℕ} {sector : Sector} :
    sector ∈ enumeratedSectors n K ↔ (⟨n, K, sector⟩ : RunSpec) ∈ sectorSpecs n K := by
  simp only [enumeratedSectors, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨spec, hm, he⟩
    obtain ⟨hn, hK⟩ := sectorSpecs_fields hm
    cases spec with
    | mk a b sec =>
      simp only at hn hK he
      subst a b sec
      exact hm
  · intro hm
    exact ⟨⟨n, K, sector⟩, hm, rfl⟩

/-- Connected sources, indexed by the finite canonical source-sector enumeration. -/
abbrev PartitionedSource (n K : ℕ) :=
  (sector : ↥(enumeratedSectors n K)) × ConnectedSource ⟨n, K, sector.val⟩

/-- Forget source metadata and reconstruct its original connected matching pair. -/
def partitionedSourceToClosed {n K : ℕ} (s : PartitionedSource n K) : ClosedMeander n :=
  ⟨s.2.val.matchings, s.2.property⟩

/-- Uniqueness of first height and of source reconstruction makes forgetting
sector metadata injective. No native evaluator is used. -/
theorem partitionedSourceToClosed_injective (n K : ℕ) :
    Function.Injective (@partitionedSourceToClosed n K) := by
  rintro ⟨sector, s⟩ ⟨other, t⟩ he
  have hm : s.val.matchings = t.val.matchings := congrArg Subtype.val he
  have hs := s.val.inSector
  have ht := t.val.inSector
  rw [← hm] at ht
  have hsector : sector = other := Subtype.ext (inSector_unique hs ht)
  subst other
  have hsrc : s.val = t.val := by
    apply (sourceEquiv _).injective
    apply Subtype.ext
    exact (sourceEquiv_matchings _ s.val).trans
      (hm.trans (sourceEquiv_matchings _ t.val).symm)
  have hst : s = t := Subtype.ext hsrc
  subst t
  rfl

/-- The original source partition supplies every public connected matching pair. -/
theorem partitionedSourceToClosed_surjective {n K : ℕ}
    (hn : 0 < n) (hK : 0 < K) (hKn : K ≤ n) :
    Function.Surjective (@partitionedSourceToClosed n K) := by
  intro p
  obtain ⟨sector, hm, hs⟩ := exists_enumerated_sector hn hK hKn p.val.1 p.val.2
  let spec : RunSpec := ⟨n, K, sector⟩
  let s : Source spec := (sourceEquiv spec).symm ⟨p.val, hs⟩
  have hsrc : s.matchings = p.val := by
    rw [← sourceEquiv_matchings spec s]
    exact congrArg Subtype.val ((sourceEquiv spec).apply_symm_apply ⟨p.val, hs⟩)
  refine ⟨⟨⟨sector, mem_enumeratedSectors.mpr hm⟩, ⟨s, ?_⟩⟩, ?_⟩
  · rw [hsrc]
    exact p.property
  · exact Subtype.ext hsrc

/-- Positive-rank connected source sectors partition the public closed objects. -/
noncomputable def sourcePartitionEquiv {n K : ℕ}
    (hn : 0 < n) (hK : 0 < K) (hKn : K ≤ n) :
    PartitionedSource n K ≃ ClosedMeander n :=
  Equiv.ofBijective partitionedSourceToClosed
    ⟨partitionedSourceToClosed_injective n K,
      partitionedSourceToClosed_surjective hn hK hKn⟩

/-- Any original matching-pair weight sums exactly over the canonical connected
source sectors. The ordinary and lower-exterior channels are two instances. -/
theorem connectedSource_partition_sum {n K : ℕ}
    (hn : 0 < n) (hK : 0 < K) (hKn : K ≤ n)
    (weight : NoncrossingMatching n × NoncrossingMatching n → ℕ) :
    (∑ sector : ↥(enumeratedSectors n K),
      ∑ s : ConnectedSource ⟨n, K, sector.val⟩, weight s.val.matchings) =
      ∑ p : ClosedMeander n, weight p.val := by
  classical
  calc
    _ = ∑ s : PartitionedSource n K, weight s.2.val.matchings :=
      (Fintype.sum_sigma (fun s : PartitionedSource n K => weight s.2.val.matchings)).symm
    _ = _ := Fintype.sum_equiv (sourcePartitionEquiv hn hK hKn) _ _ (fun _ => rfl)

/-- The ordinary source channel is exactly the public positive-rank closed count. -/
theorem connectedSource_card_sum {n K : ℕ}
    (hn : 0 < n) (hK : 0 < K) (hKn : K ≤ n) :
    (∑ sector : ↥(enumeratedSectors n K),
      Fintype.card (ConnectedSource ⟨n, K, sector.val⟩)) = closedMeanderNumber n := by
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    closedMeanderNumber] using connectedSource_partition_sum hn hK hKn (fun _ => 1)

/-- The lower-exterior source channel is exactly public even Open, using the
fixed lower-side marking equivalence and its existing cardinal sum theorem. -/
theorem connectedSource_exterior_sum {n K : ℕ}
    (hn : 0 < n) (hK : 0 < K) (hKn : K ≤ n) :
    (∑ sector : ↥(enumeratedSectors n K),
      ∑ s : ConnectedSource ⟨n, K, sector.val⟩, s.val.matchings.2.exteriorArches.card) =
      openMeanderNumber (2 * n) := by
  exact (connectedSource_partition_sum hn hK hKn
    (fun p => p.2.exteriorArches.card)).trans (openMeanderNumber_even hn).symm

/-- Projection to sector names remains injective because rank and threshold are fixed. -/
theorem sectorSpecs_sector_nodup (n K : ℕ) :
    ((sectorSpecs n K).map RunSpec.sector).Nodup := by
  apply (sectorSpecs_nodup n K).map_on
  intro a ha b hb he
  obtain ⟨han, haK⟩ := sectorSpecs_fields ha
  obtain ⟨hbn, hbK⟩ := sectorSpecs_fields hb
  cases a
  cases b
  simp only at han haK hbn hbK he
  subst_vars
  rfl

/-- Source-sector sums agree with the evaluator's exact duplicate-free list order. -/
theorem sectorSpecs_sum (n K : ℕ) (f : RunSpec → ℕ) :
    ((sectorSpecs n K).map f).sum =
      ∑ sector : ↥(enumeratedSectors n K), f ⟨n, K, sector.val⟩ := by
  classical
  have he : (sectorSpecs n K).map f =
      ((sectorSpecs n K).map RunSpec.sector).map (fun sector => f ⟨n, K, sector⟩) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro spec hs
    obtain ⟨hn, hK⟩ := sectorSpecs_fields hs
    cases spec with
    | mk a b sector =>
      simp only at hn hK
      subst a b
      rfl
  rw [he, ← List.sum_toFinset _ (sectorSpecs_sector_nodup n K)]
  exact (Finset.sum_coe_sort _ _).symm

/-- Ordinary connected-source cardinalities in the precise evaluator list order
sum to the public closed-meander number. -/
theorem sectorSpecs_closed_sum {n K : ℕ}
    (hn : 0 < n) (hK : 0 < K) (hKn : K ≤ n) :
    ((sectorSpecs n K).map fun spec => Fintype.card (ConnectedSource spec)).sum =
      closedMeanderNumber n := by
  rw [sectorSpecs_sum]
  exact connectedSource_card_sum hn hK hKn

/-- Lower-exterior connected-source weights in the precise evaluator list order
sum to public even Open, preserving the designated lower-side convention. -/
theorem sectorSpecs_open_sum {n K : ℕ}
    (hn : 0 < n) (hK : 0 < K) (hKn : K ≤ n) :
    ((sectorSpecs n K).map fun spec =>
      ∑ s : ConnectedSource spec, s.val.matchings.2.exteriorArches.card).sum =
      openMeanderNumber (2 * n) := by
  rw [sectorSpecs_sum]
  exact connectedSource_exterior_sum hn hK hKn

end Meanders.FirstCrossing
