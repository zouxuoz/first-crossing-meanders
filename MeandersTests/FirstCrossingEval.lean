import Meanders.Certify.Examples.FirstCrossingClosed2
import Meanders.Certify.Examples.FirstCrossingOpen2
import Meanders.Certify.Examples.FirstCrossingOpen4
import Meanders.Certify.FirstCrossing.Replay
import Meanders.Certify.FirstCrossing.CountReplay
import Meanders.Algorithms.FirstCrossing
import Meanders.Models.FirstCrossing.Correctness.Future
import Meanders.Verification.KnownValues
import Meanders.Models.FirstCrossing.Correctness.AcceptedWeight

/-! Compiled reference regressions and exact history/observer axiom snapshots. -/
set_option linter.hashCommand false

open Meanders.FirstCrossing

#guard (List.range 5).map (fun n => (evaluate n).closed) = [0, 1, 2, 8, 42]
#guard (List.range 5).map (fun n => (evaluate n).openEven) = [1, 1, 3, 14, 81]
#guard (evaluate 0).openOddPrevious = none
#guard (evaluate 4).openOddPrevious = some 42
#guard (List.range 4).all (fun k => runAtThreshold 4 (k + 1) == (42, 81))

/-- info: 'Meanders.FirstCrossing.jointLayer_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.jointLayer_invariant

/-- info: 'Meanders.FirstCrossing.NativeHistory.source_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.NativeHistory.source_unique

/-- info: 'Meanders.FirstCrossing.AcceptedWord.event_exterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.AcceptedWord.event_exterior

#guard Meanders.Verification.agreesWithKnown .closed (count .closed) 6
#guard Meanders.Verification.agreesWithKnown .open (count .open) 12

/-- info: 'Meanders.FirstCrossing.acceptedSourceEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.acceptedSourceEquiv

/-- info: 'Meanders.FirstCrossing.stateFutureEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.stateFutureEquiv

/-- info: 'Meanders.FirstCrossing.sectorSpecs_closed_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.sectorSpecs_closed_sum

/-- info: 'Meanders.FirstCrossing.sectorSpecs_open_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.sectorSpecs_open_sum

/-- info: 'Meanders.FirstCrossing.evaluateJoint_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.evaluateJoint_correct

/-- info: 'Meanders.FirstCrossing.count_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.count_eq

/-- info: 'Meanders.Certify.KernelSort.sort_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.Certify.KernelSort.sort_eq

/-- info: 'Meanders.Certify.FirstCrossingRun.replayCount_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.Certify.FirstCrossingRun.replayCount_eq

/-- info: 'Meanders.Certify.CountCertificate.correct_of_firstCrossingCount' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Meanders.Certify.CountCertificate.correct_of_firstCrossingCount

/-- info: 'Meanders.Certify.FirstCrossingSectorTable.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.Certify.FirstCrossingSectorTable.check_sound

/-- info: 'Meanders.Certify.FirstCrossingRun.check_joint_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.Certify.FirstCrossingRun.check_joint_correct

/-- info: 'Meanders.Certify.FirstCrossingRun.Certificate.claim?_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.Certify.FirstCrossingRun.Certificate.claim?_sound

/-- info: 'Meanders.Certify.FirstCrossingRun.Certificate.replayClaim?_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.Certify.FirstCrossingRun.Certificate.replayClaim?_eq

/-- info: 'Meanders.Certify.FirstCrossingRun.Certificate.replayClaim?_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Meanders.Certify.FirstCrossingRun.Certificate.replayClaim?_sound

/-- info: 'Meanders.Certified.first_crossing_closed_n2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.Certified.first_crossing_closed_n2

/-- info: 'Meanders.Certified.first_crossing_open_n2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.Certified.first_crossing_open_n2

/-- info: 'Meanders.Certified.first_crossing_open_n4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.Certified.first_crossing_open_n4
