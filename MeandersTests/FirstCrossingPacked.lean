import Meanders.Models.FirstCrossing.Packed.Correct

/-! Oriented packed representation axiom snapshots. -/
set_option linter.hashCommand false

/-- info: 'Meanders.NoncrossingMatching.partnerOf_wordOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.NoncrossingMatching.partnerOf_wordOf

/-- info: 'Meanders.NoncrossingMatching.leftPartnerOf_wordOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.NoncrossingMatching.leftPartnerOf_wordOf

/-- info: 'Meanders.FirstCrossing.Packed.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.Packed.decode_encode

/-- info: 'Meanders.FirstCrossing.Packed.encode_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.Packed.encode_decode

/-- info: 'Meanders.FirstCrossing.Packed.encode_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.Packed.encode_bit

/-- info: 'Meanders.FirstCrossing.Packed.decode_wordSuccessors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.Packed.decode_wordSuccessors

/-- info: 'Meanders.FirstCrossing.Packed.wordEncode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.Packed.wordEncode_injective

/-- info: 'Meanders.FirstCrossing.Packed.wordSuccessors_none_of_schedule_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Meanders.FirstCrossing.Packed.wordSuccessors_none_of_schedule_none
