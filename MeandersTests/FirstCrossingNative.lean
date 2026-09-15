import Meanders.Models.FirstCrossing.Surgery.NativeTotal
import Meanders.Models.FirstCrossing.Surgery.VisitCoverage
import Meanders.Models.FirstCrossing.Surgery.PhysicalCyclic
import Meanders.Models.FirstCrossing.Surgery.DrainTotal
import Meanders.Models.FirstCrossing.Native.Geometry
import Meanders.Models.FirstCrossing.Native.State
import Meanders.Models.FirstCrossing.Interpretation.FIFO
import Meanders.Models.FirstCrossing.Native.Codec
import Meanders.Models.FirstCrossing.Native.PortBound
import Meanders.Models.FirstCrossing.Native.Stage
import Meanders.Models.FirstCrossing.Surgery.Normalize
import Meanders.Models.FirstCrossing.Surgery.Cup
import Meanders.Models.FirstCrossing.Surgery.Coverage
import Meanders.Models.FirstCrossing.Surgery.Drain

/-! Native First-Crossing malformed-state and transition regressions. -/

set_option linter.hashCommand false

namespace MeandersTests.FirstCrossingNative

open Meanders.FirstCrossing

-- Malformed raw pairings and forged progress must not enter the recurrence.
#guard !(validKey ⟨2, 2, .low⟩ ⟨1, 1, 0⟩ ⟨⟨0, 0, 0, 0⟩, [0, 1]⟩)
#guard !(validKey ⟨2, 2, .low⟩ ⟨1, 1, 0⟩ ⟨⟨0, 0, 0, 0⟩, [9, 0]⟩)
#guard !(validKey ⟨2, 2, .low⟩ ⟨1, 0, 1⟩ ⟨⟨0, 0, 0, 0⟩, [1, 0]⟩)
#guard !(validKey ⟨3, 2, .low⟩ ⟨2, 2, 0⟩ ⟨⟨1, 0, 1, 0⟩, []⟩)
#guard !(validKey ⟨2, 2, .low⟩ ⟨1, 1, 0⟩ ⟨⟨2, 0, 0, 0⟩, [1, 0]⟩)
#guard rawStep ⟨1, 1, .high 1 1 1⟩ ⟨1, 1, 0⟩ ⟨Counters.zero, [1, 0]⟩ .UU =
  some ⟨Counters.zero, []⟩
#guard lowerIncrement ⟨5, 2, 3⟩ ⟨⟨0, 1, 0, 0⟩, [1, 0]⟩ .UD .right = 0
#guard rawStep ⟨2, 1, .high 1 1 1⟩ ⟨2, 0, 2⟩ ⟨Counters.zero, [2, 3, 0, 1]⟩ .UU = none
#guard rawStep ⟨6, 3, .high 4 2 4⟩ ⟨8, 3, 5⟩ ⟨⟨1, 2, 0, 1⟩, [1, 0, 3, 2]⟩ .UU = none

-- A valid involution can still cross in the actual cyclic order rev(PL), QL.
#guard pairingValid [3, 2, 1, 0]
#guard !(validKey ⟨4, 3, .low⟩ ⟨2, 2, 0⟩ ⟨Counters.zero, [3, 2, 1, 0]⟩)
#guard validKey ⟨4, 3, .low⟩ ⟨2, 2, 0⟩ ⟨Counters.zero, [2, 3, 0, 1]⟩

end MeandersTests.FirstCrossingNative

set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- info: 'Meanders.FirstCrossing.firstHeightCounters' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.firstHeightCounters

/-- info: 'Meanders.FirstCrossing.forcedFIFO_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.forcedFIFO_sound

/-- info: 'Meanders.FirstCrossing.emitted_next_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.emitted_next_between

/-- info: 'Meanders.FirstCrossing.cyclicCheck_iff_noncrossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.cyclicCheck_iff_noncrossing

/-- info: 'Meanders.FirstCrossing.decodeKey_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.decodeKey_roundtrip

/-- info: 'Meanders.FirstCrossing.decodeKey_storage_partner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.decodeKey_storage_partner

/-- info: 'Meanders.FirstCrossing.high_geometry_port_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.high_geometry_port_bound

/-- info: 'Meanders.FirstCrossing.low_geometry_port_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.low_geometry_port_bound

/-- info: 'Meanders.FirstCrossing.Stage.valid_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.Stage.valid_next

/-- info: 'Meanders.FirstCrossing.spliceJoin_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.spliceJoin_represents

/-- info: 'Meanders.FirstCrossing.spliceJoin_cycle_iff_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.spliceJoin_cycle_iff_reachable

/-- info: 'Meanders.FirstCrossing.candidateCup_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.candidateCup_represents

/-- info: 'Meanders.FirstCrossing.normalize_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.normalize_total

/-- info: 'Meanders.FirstCrossing.normalize_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.normalize_represents

/-- info: 'Meanders.FirstCrossing.CoversProcessed.connected_of_one_cycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.CoversProcessed.connected_of_one_cycle

/-- info: 'Meanders.FirstCrossing.drain_small_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.drain_small_preserves

/-- info: 'Meanders.FirstCrossing.joined_next_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.joined_next_between

/-- info: 'Meanders.FirstCrossing.spliceJoin_cyclicCheck_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.spliceJoin_cyclicCheck_adjacent

/-- info: 'Meanders.FirstCrossing.candidate_physical_cyclic_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.candidate_physical_cyclic_total

/-- info: 'Meanders.FirstCrossing.drain_one_total_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.drain_one_total_upper

/-- info: 'Meanders.FirstCrossing.drain_one_total_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.drain_one_total_lower

/-- info: 'Meanders.FirstCrossing.geometry_length_next_conservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.geometry_length_next_conservation

/-- info: 'Meanders.FirstCrossing.normalize_cyclicCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.normalize_cyclicCheck

/-- info: 'Meanders.FirstCrossing.rawStep_total_before_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.rawStep_total_before_cycles

/-- info: 'Meanders.FirstCrossing.attachOwner_represents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.attachOwner_represents

/-- info: 'Meanders.FirstCrossing.physical_visit_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.physical_visit_preserves

/-- info: 'Meanders.FirstCrossing.candidateSplice_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.FirstCrossing.candidateSplice_stages
