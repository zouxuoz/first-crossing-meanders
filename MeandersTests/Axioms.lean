import Meanders

/-!
# Axiom snapshots

General declaration snapshots; model-specific snapshots live in the corresponding
test modules. Only Lean's classical axioms `propext`, `Classical.choice`, and
`Quot.sound` are permitted; each block records the actual dependencies.
-/

-- These snapshot tests intentionally nest `#print axioms` inside `#guard_msgs`.
set_option linter.hashCommand false
set_option linter.style.whitespace false
-- Keep their exact one-line output easy to update and compare.
set_option linter.style.longLine false

/-- info: 'Meanders.card_noncrossingMatching_eq_catalan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.card_noncrossingMatching_eq_catalan

/-- info: 'Meanders.equivDyckWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.equivDyckWord

/-- info: 'Meanders.countClosedMeanders_eq_closedMeanderNumber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.countClosedMeanders_eq_closedMeanderNumber

/-- info: 'Meanders.countOpenMeanders_eq_openMeanderNumber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.countOpenMeanders_eq_openMeanderNumber

/-- info: 'Meanders.Certify.CountCertificate.check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.Certify.CountCertificate.check_iff

/-- info: 'Meanders.Certify.verifyString_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.Certify.verifyString_sound

/-- info: 'Meanders.cutGraph_connected_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.cutGraph_connected_iff

/-- info: 'Meanders.NoncrossingMatching.mem_exteriorArches_iff_active_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Meanders.NoncrossingMatching.mem_exteriorArches_iff_active_empty

/-- info: 'Meanders.oddOpenClosedEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.oddOpenClosedEquiv

/-- info: 'Meanders.evenOpenClosedEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.evenOpenClosedEquiv

/-- info: 'Meanders.openMeanderNumber_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.openMeanderNumber_odd

/-- info: 'Meanders.openMeanderNumber_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Meanders.openMeanderNumber_even

