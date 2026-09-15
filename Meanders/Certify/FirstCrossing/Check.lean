import Meanders.Certify.FirstCrossing.Metadata
import Meanders.Certify.FirstCrossing.Sector

/-! Exact all-sector layer checking against the native joint reference. -/

namespace Meanders.Certify.FirstCrossingRun

open FirstCrossing

/-- Pass every independent sector channel to the existing exact terminal checker. -/
def SectorSummary.toSummary (s : SectorSummary) : FirstCrossingSectorTable.Summary :=
  ⟨s.ordinary, s.lowerReturns, s.bonusContribution, s.lowerReturns + s.bonusContribution⟩

/-- Consume the flat sector-major evidence using the shared exact sector cursor.
Evidence is neither sorted nor merged, and the first failure stops the check. -/
def checkSectorsWith (sectorCheck : RunSpec → List FirstCrossing.Layer →
    FirstCrossingSectorTable.Summary → Except String FirstCrossingSectorTable.Summary) :
    List RunSpec → List SectorSummary → List FirstCrossing.Layer →
    Except String Counts
  | [], [], [] => .ok (0, 0)
  | [], _, _ => .error "extra First-Crossing summaries or layers"
  | _ :: _, [], _ => .error "missing First-Crossing sector summary"
  | spec :: specs, summary :: summaries, layers =>
    if summary.sector = spec.sector then
      match sectorCheck spec (layers.take (2 * spec.n + 1))
          summary.toSummary with
      | .error e => .error e
      | .ok result =>
        match checkSectorsWith sectorCheck specs summaries (layers.drop (2 * spec.n + 1)) with
        | .error e => .error e
        | .ok tail => .ok (result.ordinary + tail.1, result.openEven + tail.2)
    else .error "First-Crossing sector identity mismatch"

/-- The ordinary checker uses the existing exact reference-sector cursor. -/
abbrev checkSectors := checkSectorsWith FirstCrossingSectorTable.check

/-- Successful flat evidence has the sum of the actual reference sector results. -/
theorem checkSectors_sound {specs : List RunSpec} {summaries : List SectorSummary}
    {layers : List FirstCrossing.Layer} {result : Counts}
    (h : checkSectors specs summaries layers = .ok result) :
    result = ((specs.map fun s => (runSector s).1).sum,
      (specs.map fun s => (runSector s).2).sum) := by
  induction specs generalizing summaries layers result with
  | nil =>
    cases summaries <;> cases layers <;> simp_all [checkSectors, checkSectorsWith]
  | cons spec specs ih =>
    cases summaries with
    | nil => simp [checkSectors, checkSectorsWith] at h
    | cons summary summaries =>
      simp only [checkSectors, checkSectorsWith] at h
      split at h
      · cases hs : FirstCrossingSectorTable.check spec
            (layers.take (2 * spec.n + 1)) summary.toSummary with
        | error e => simp [hs] at h
        | ok sector =>
          simp only [hs] at h
          cases ht : checkSectors specs summaries (layers.drop (2 * spec.n + 1)) with
          | error e => simp [ht] at h
          | ok tail =>
            simp only [ht, Except.ok.injEq] at h
            subst result
            have hsector := FirstCrossingSectorTable.check_sound hs
            have htail := ih ht
            have hc : sector.ordinary = (runSector spec).1 := congrArg Prod.fst hsector
            have he : sector.openEven = (runSector spec).2 := congrArg Prod.snd hsector
            simp only [List.map_cons, List.sum_cons]
            simp only [htail, hc, he]
      · cases h

/-- Check structure and then every sector; the public zero convention has no
rank-zero carrier trace. Joint claimed fields are compared to the checked pair. -/
def checkWith (sectorCheck : RunSpec → List FirstCrossing.Layer →
    FirstCrossingSectorTable.Summary → Except String FirstCrossingSectorTable.Summary)
    (m : Metadata) (layers : List FirstCrossing.Layer) : Except String Counts :=
  match m.validateLayerCount layers.length with
  | .error e => .error e
  | .ok () =>
    match m.validate with
    | .error e => .error e
    | .ok () =>
      if m.nativeOrder = 0 then
        if layers.isEmpty then .ok (0, 1)
        else .error "rank-zero First-Crossing evidence must have no layers"
      else
        match checkSectorsWith sectorCheck
            (sectorSpecs m.nativeOrder m.threshold) m.sectors layers with
        | .error e => .error e
        | .ok result =>
          if result = (m.closed, m.openEven) then .ok result
          else .error "First-Crossing checked joint total mismatch"

/-- Public loaded checking specializes to the actual native reference sector checker. -/
abbrev check := checkWith FirstCrossingSectorTable.check

/-- Success proves the joint numerical reference result at the explicitly supplied
threshold; its public Closed/Open interpretation is a separate theorem boundary. -/
theorem check_sound {m : Metadata} {layers : List FirstCrossing.Layer} {result : Counts}
    (h : check m layers = .ok result) :
    result = if m.nativeOrder = 0 then (0, 1)
      else runAtThreshold m.nativeOrder m.threshold := by
  unfold check checkWith at h
  cases hl : m.validateLayerCount layers.length with
  | error e => simp [hl] at h
  | ok value =>
    cases value
    simp only [hl] at h
    cases hv : m.validate with
    | error e => simp [hv] at h
    | ok value =>
      cases value
      simp only [hv] at h
      split at h
      · split at h
        · simp_all
        · cases h
      · rename_i hn
        cases hs : checkSectors (sectorSpecs m.nativeOrder m.threshold) m.sectors layers with
        | error e => simp [hs] at h
        | ok pair =>
          simp only [hs] at h
          split at h
          · cases h
            rw [ite_eq_right hn, runAtThreshold_pair]
            exact checkSectors_sound hs
          · cases h

end Meanders.Certify.FirstCrossingRun
