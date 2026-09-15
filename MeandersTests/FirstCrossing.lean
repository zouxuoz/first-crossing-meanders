import Meanders.Models.FirstCrossing.Interpretation.SourceCycle
import Meanders.Models.FirstCrossing.Interpretation.SourceCoverage
import Meanders.Models.FirstCrossing.Interpretation.Preservation
import Meanders.Models.FirstCrossing.Interpretation.AttachmentStep
import Meanders.Models.FirstCrossing.Interpretation.Boundary
import Meanders.Models.FirstCrossing.Interpretation.SourceStep
import Meanders.Models.FirstCrossing.Interpretation.SourceProgress
import Meanders.Models.FirstCrossing.Interpretation.Invariant
import Meanders.Models.FirstCrossing.Surgery.Closure
import Meanders.Models.FirstCrossing.Original.Schedule
import Meanders.Models.FirstCrossing.Original.Exterior
import Meanders.Models.FirstCrossing.Original.ForcedPrefix
import Meanders.Models.FirstCrossing.Original.Pairing

/-! Concrete source/cut regressions and the First-Crossing axiom snapshot. -/

set_option linter.hashCommand false

namespace MeandersTests.FirstCrossing

open Meanders Meanders.FirstCrossing DyckStep

private def empty : NoncrossingMatching 0 := ofDyck (w := []) (by decide)
private def nested : NoncrossingMatching 3 := ofDyck (w := [U, U, U, D, D, D]) (by decide)
private def separate : NoncrossingMatching 3 := ofDyck (w := [U, D, U, D, U, D]) (by decide)
private def asymmetric : NoncrossingMatching 3 := ofDyck (w := [U, U, D, D, U, D]) (by decide)

#guard InSector 1 empty empty .low
#guard Sector.low.schedule 0 = []

-- The same source changes its first-hit cut with the threshold.
#guard InSector 1 nested nested (.high 1 1 1)
#guard InSector 2 nested nested (.high 2 2 2)
#guard InSector 3 nested nested (.high 3 3 3)
#guard InSector 2 separate separate .low
#guard ¬ InSector 2 nested nested (.high 3 3 3)
#guard ¬ InSector 1 nested nested (.high 2 2 2)

-- Asymmetric inward reads use physical reverse-complement on the right.
#guard (leftHalf (by decide) (⟨asymmetric, by decide⟩ : MatchingAtCut 3 1 1)).word = [U]
#guard (rightHalf (by decide) (⟨asymmetric, by decide⟩ : MatchingAtCut 3 1 1)).word =
  [U, D, U, U, D]
#guard (leftHalf (by decide) (⟨asymmetric, by decide⟩ : MatchingAtCut 3 5 1)).word =
  [U, U, D, D, U]
#guard (rightHalf (by decide) (⟨asymmetric, by decide⟩ : MatchingAtCut 3 5 1)).word = [U]
#guard (leftHalf (by decide) (⟨asymmetric, by decide⟩ : MatchingAtCut 3 0 0)).word = []
#guard (rightHalf (by decide) (⟨asymmetric, by decide⟩ : MatchingAtCut 3 6 0)).word = []

-- Both long-side orientations, the midpoint tie and zero-length skirts.
#guard (Sector.high 2 2 2).schedule 3 = [.right, .right, .left, .right, .left, .right]
#guard (Sector.high 4 2 2).schedule 3 = [.left, .left, .right, .left, .right, .left]
#guard (Sector.high 3 1 3).schedule 3 = [.left, .right, .left, .right, .left, .right]
#guard (Sector.high 1 1 1).schedule 1 = [.left, .right]
#guard (Sector.high 2 2 2).budgets 3 = (0, 1, 0, 1)
#guard (Sector.high 4 2 2).budgets 3 = (1, 0, 1, 0)

-- Every cut of every small matching, including both endpoints and zero height.
#guard ∀ (m : NoncrossingMatching 4) (cut : Fin 9),
  m.exteriorArches.card =
    Fintype.card (ReturnEvent (m.wordOf.take cut.val)) +
    Fintype.card (ReturnEvent (Dyck.reverseComplement (m.wordOf.drop cut.val))) +
    if 0 < height m.wordOf cut.val then 1 else 0

-- Original height three is not an exterior return, even when one port is retained.
#guard Fintype.card (ReturnEvent [U, U, U, D]) = 0
#guard Fintype.card (ReturnEvent [U, D]) = 1
-- Equal final heights can carry different past exterior weights.
#guard Dyck.height [U, U, D] = Dyck.height [U, D, U]
#guard Fintype.card (ReturnEvent [U, U, D]) = 0
#guard Fintype.card (ReturnEvent [U, D, U]) = 1

#guard Fintype.card (ReturnEvent nested.wordOf) = 1
#guard Fintype.card (ReturnEvent separate.wordOf) = 3
#guard ∀ (m : NoncrossingMatching 4), m.reflect.exteriorArches.card = m.exteriorArches.card

-- Closing one represented path retains all other frontier paths for later policy checks.
#guard (adjacentCap separate).1 = true
#guard ∀ i : Fin 4, (adjacentCap separate).2.partnerIndex i = [1, 0, 3, 2][i.val]!
#guard (adjacentCap nested).1 = false
#guard ∀ i : Fin 4, (adjacentCap nested).2.partnerIndex i = [1, 0, 3, 2][i.val]!
#guard (adjacentCap (adjacentCup empty)).1 = true
#guard ∀ m : NoncrossingMatching 3, (adjacentCap (adjacentCup m)).2 = m

-- Sharp suffix witnesses cover unused height and descent all the way to zero.
#guard lowestSuffix 4 5 2 = [D, D, U, U, U]
#guard lowestSuffix 1 5 3 = [D, U, U, D, D]
#guard lowestSuffix 0 4 2 = [U, U, D, D]
#guard (nextPort 6)^[5] 0 = 5 ∧ (nextPort 6)^[5] 1 = 0

end MeandersTests.FirstCrossing

set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- info: 'Meanders.FirstCrossing.firstHeightPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.firstHeightPartition

/-- info: 'Meanders.FirstCrossing.asymmetricCutEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.asymmetricCutEquiv

/-- info: 'Meanders.FirstCrossing.through_pair_ordinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.through_pair_ordinal

/-- info: 'Meanders.FirstCrossing.inSector_high_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.inSector_high_admissible

/-- info: 'Meanders.FirstCrossing.Sector.schedule_high_count_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Sector.schedule_high_count_left

/-- info: 'Meanders.FirstCrossing.Sector.schedule_high_count_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Sector.schedule_high_count_right

/-- info: 'Meanders.FirstCrossing.exteriorArchCutEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.exteriorArchCutEquiv

/-- info: 'Meanders.FirstCrossing.exteriorCount_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.exteriorCount_cut

/-- info: 'Meanders.FirstCrossing.exteriorReflectionEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.exteriorReflectionEquiv

/-- info: 'Meanders.FirstCrossing.exteriorCut_reflection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.exteriorCut_reflection

/-- info: 'Meanders.FirstCrossing.forcedPrefix_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.forcedPrefix_exact

/-- info: 'Meanders.FirstCrossing.forcedOpenings_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.forcedOpenings_card

/-- info: 'Meanders.FirstCrossing.adjacentCup_representsPaths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.adjacentCup_representsPaths

/-- info: 'Meanders.FirstCrossing.adjacentCap_representsPaths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.adjacentCap_representsPaths

/-- info: 'Meanders.FirstCrossing.adjacentCap_closes_iff_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.adjacentCap_closes_iff_reachable

/-- info: 'Meanders.FirstCrossing.iterate_rotate_representsPaths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.iterate_rotate_representsPaths

/-- info: 'Meanders.FirstCrossing.iterate_nextPort_seam' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.iterate_nextPort_seam

/-- info: 'Meanders.FirstCrossing.sourceEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.sourceEquiv

/-- info: 'Meanders.FirstCrossing.incidenceGraph_connected_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.incidenceGraph_connected_iff

/-- info: 'Meanders.FirstCrossing.Source.retainedBoundary_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.retainedBoundary_length

/-- info: 'Meanders.FirstCrossing.Source.partialGraph_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.partialGraph_degree

/-- info: 'Meanders.FirstCrossing.Source.representsKey_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.representsKey_empty

/-- info: 'Meanders.FirstCrossing.saturatedComponent_permanent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.saturatedComponent_permanent

/-- info: 'Meanders.FirstCrossing.degreeTwoComponent_not_connected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.degreeTwoComponent_not_connected

/-- info: 'Meanders.FirstCrossing.Source.mem_retainedBoundary_iff_degree_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.mem_retainedBoundary_iff_degree_one

/-- info: 'Meanders.FirstCrossing.Source.retainedBoundary_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.retainedBoundary_nodup

/-- info: 'Meanders.FirstCrossing.Source.RepresentsKey.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.RepresentsKey.unique

/-- info: 'Meanders.FirstCrossing.Source.counters_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.counters_valid

/-- info: 'Meanders.FirstCrossing.Source.prefix_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.prefix_allowed

/-- info: 'Meanders.FirstCrossing.Source.ofTick_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.ofTick_progress

/-- info: 'Meanders.FirstCrossing.Source.partialGraph_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.partialGraph_end

/-- info: 'Meanders.FirstCrossing.Source.nextMove_allowed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.nextMove_allowed

/-- info: 'Meanders.FirstCrossing.Source.partialGraph_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.partialGraph_next

/-- info: 'Meanders.FirstCrossing.Source.visitEdges_not_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.visitEdges_not_old

/-- info: 'Meanders.FirstCrossing.Source.throughAdded_heads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.throughAdded_heads

/-- info: 'Meanders.FirstCrossing.Source.drain_heads_source_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.drain_heads_source_edge

/-- info: 'Meanders.FirstCrossing.Source.attachOwners_groups_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.attachOwners_groups_map

/-- info: 'Meanders.FirstCrossing.Source.drains_groups_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.drains_groups_map

/-- info: 'Meanders.FirstCrossing.initial_validKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.initial_validKey

/-- info: 'Meanders.FirstCrossing.Source.RepresentsKey.canonical_invariants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.RepresentsKey.canonical_invariants

/-- info: 'Meanders.FirstCrossing.Source.RepresentsKey.rawStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.RepresentsKey.rawStep

/-- info: 'Meanders.FirstCrossing.closing_component_degree_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.closing_component_degree_two

/-- info: 'Meanders.FirstCrossing.closing_incidence_component_permanent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.closing_incidence_component_permanent

/-- info: 'Meanders.FirstCrossing.Source.RepresentsKey.nextMove_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.RepresentsKey.nextMove_total

/-- info: 'Meanders.FirstCrossing.Source.CoveredKey.rawStep_terminal_connected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Source.CoveredKey.rawStep_terminal_connected
