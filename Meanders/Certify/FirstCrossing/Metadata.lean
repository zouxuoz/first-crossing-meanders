import Meanders.Certify.Json

namespace Meanders.Certify.FirstCrossingRun

open FirstCrossing

/-- One ordered sector summary; lower returns remain unbonused. -/
structure SectorSummary where
  /-- Oriented LOW/HIGH source identity. -/
  sector : Sector
  /-- Ordinary terminal multiplicity. -/
  ordinary : ℕ
  /-- Original lower-return first moment. -/
  lowerReturns : ℕ
  /-- Exactly the single through bonus multiplied by ordinary multiplicity. -/
  bonusContribution : ℕ
  deriving DecidableEq, Repr

/-- Optional semantic extension, present only for First-Crossing layer evidence. -/
structure Metadata where
  /-- Native closed order, independent of the public open-crossing index. -/
  nativeOrder : ℕ
  /-- First-height threshold; zero only at rank zero. -/
  threshold : ℕ
  /-- Joint ordinary total across all sectors. -/
  closed : ℕ
  /-- Joint lower exterior total across all sectors. -/
  openEven : ℕ
  /-- Exact LOW-then-HIGH order from sectorSpecs, including source-empty sectors. -/
  sectors : List SectorSummary
  deriving DecidableEq, Repr

/-- The new row/transition contract; prior count runs remain accepted for this producer. -/
def representation : String := "first-crossing-lower-jet"

/-- Canonical identity and summary bytes for one ordered source sector. -/
def SectorSummary.header (s : SectorSummary) : String :=
  let identity := match s.sector with
    | .low => "sector\nlow\n"
    | .high cut upper lower => s!"sector\nhigh\n{cut}\n{upper}\n{lower}\n"
  identity ++ s!"{s.ordinary}\n{s.lowerReturns}\n{s.bonusContribution}\n"

/-- Appended semantic bytes bind joint totals and every ordered sector summary. -/
def Metadata.header (m : Metadata) : String :=
  s!"first-crossing\n{m.nativeOrder}\n{m.threshold}\n{m.closed}\n{m.openEven}\n" ++
    s!"{m.sectors.length}\n" ++ String.join (m.sectors.map SectorSummary.header)

/-- Reject impossible evidence sizes before enumerating any source sectors.
Positive order always includes LOW, even when its source language is empty. -/
def Metadata.validateLayerCount (m : Metadata) (layers : Nat) : Except String Unit := do
  if m.nativeOrder > 0 && m.sectors.isEmpty then
    throw "positive-order First-Crossing evidence must include sectors"
  if layers != m.sectors.length * (2 * m.nativeOrder + 1) then
    throw "wrong number of First-Crossing sector layers"

/-- Validate exact sector enumeration, channels, bonus arithmetic and joint totals. -/
def Metadata.validate (m : Metadata) : Except String Unit := do
  if m.nativeOrder = 0 then
    if m.threshold != 0 || m.closed != 0 || m.openEven != 1 || !m.sectors.isEmpty then
      throw "rank-zero First-Crossing metadata must be K=0, counts=(0,1), no sectors"
  else
    if m.threshold = 0 || m.nativeOrder < m.threshold then
      throw "invalid First-Crossing threshold"
    if m.sectors.map SectorSummary.sector !=
        (sectorSpecs m.nativeOrder m.threshold).map RunSpec.sector then
      throw "First-Crossing sectors do not match canonical enumeration"
    for s in m.sectors do
      let spec : RunSpec := ⟨m.nativeOrder, m.threshold, s.sector⟩
      if s.bonusContribution != spec.lowerBonus * s.ordinary then
        throw "First-Crossing sector bonus mismatch"
    if m.closed != (m.sectors.map SectorSummary.ordinary).sum ||
        m.openEven != (m.sectors.map fun s => s.lowerReturns + s.bonusContribution).sum then
      throw "First-Crossing joint totals do not match sector summaries"

/-- Public Closed/even Open/previous odd Open conventions select the explicit joint pair. -/
def Metadata.validateClaim (m : Metadata) (c : Claim) : Except String Unit := do
  match c.problem with
  | .closed =>
    if c.n != m.nativeOrder || c.count != m.closed then
      throw "First-Crossing closed claim mismatch"
  | .open =>
    if c.n = 2 * m.nativeOrder then
      if c.count != m.openEven then throw "First-Crossing even open claim mismatch"
    else if 0 < m.nativeOrder && c.n + 1 == 2 * m.nativeOrder then
      if c.count != m.closed then throw "First-Crossing odd open claim mismatch"
    else throw "First-Crossing public/native order mismatch"

/-- Parse only the two pinned source identity forms. -/
def sectorOfJson? (j : Lean.Json) : Except String Sector := do
  match ← j.getObjValAs? String "kind" with
  | "low" => pure .low
  | "high" => pure (.high (← j.getObjValAs? ℕ "cut")
      (← j.getObjValAs? ℕ "upper") (← j.getObjValAs? ℕ "lower"))
  | _ => throw "unknown First-Crossing sector kind"

/-- Parse one explicit original lower-return and bonus summary. -/
def SectorSummary.ofJson? (j : Lean.Json) : Except String SectorSummary := do
  pure ⟨← sectorOfJson? (← j.getObjVal? "sector"), ← j.getObjValAs? ℕ "ordinary",
    ← j.getObjValAs? ℕ "lowerReturns", ← j.getObjValAs? ℕ "bonusContribution"⟩

/-- Parse the joint First-Crossing extension with exact natural channels. -/
def Metadata.ofJson? (j : Lean.Json) : Except String Metadata := do
  pure ⟨← j.getObjValAs? ℕ "nativeOrder", ← j.getObjValAs? ℕ "threshold",
    ← j.getObjValAs? ℕ "closed", ← j.getObjValAs? ℕ "openEven",
    ← (← j.getObjValAs? (Array Lean.Json) "sectors").toList.mapM SectorSummary.ofJson?⟩

end Meanders.Certify.FirstCrossingRun
