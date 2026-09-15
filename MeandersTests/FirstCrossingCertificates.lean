import Meanders.Certify.FirstCrossing.Correct
import Meanders.Certify.FirstCrossing.Format
import Meanders.Certify.Verifier

/-! First-Crossing parser, loaded evidence and early structural rejection.
The explicit order-one table exercises the terminal HIGH bonus independently
of the producer. These guards are compiled checks, not numerical kernel proofs. -/
set_option linter.hashCommand false

namespace MeandersTests.FirstCrossingCertificates

open Meanders Meanders.Certify

private def metadata : FirstCrossingRun.Metadata :=
  ⟨1, 1, 1, 1, [⟨.low, 0, 0, 0⟩, ⟨.high 1 1 1, 1, 0, 1⟩]⟩

private def seed : FirstCrossing.Layer := [(FirstCrossing.Key.empty, (1, 0))]

private def evidence : FirstCrossingRun.Certificate :=
  { claim := ⟨.open, 2, 1⟩, metadata,
    layers := [seed, [], [], seed, [(⟨⟨0, 0, 0, 0⟩, [1, 0]⟩, (1, 0))], seed] }

private def check (c : FirstCrossingRun.Certificate) : Except String Claim :=
  c.claim?

#guard check evidence == .ok ⟨.open, 2, 1⟩
#guard check { evidence with claim := ⟨.closed, 1, 1⟩ } == .ok ⟨.closed, 1, 1⟩
#guard check { evidence with claim := ⟨.open, 1, 1⟩ } == .ok ⟨.open, 1, 1⟩
#guard check { evidence with claim := ⟨.open, 2, 2⟩ } ==
  .error "First-Crossing even open claim mismatch"
#guard check { evidence with layers := [] :: evidence.layers.tail } ==
  .error "layer 0 is not the initial state"
#guard check { evidence with layers := evidence.layers.take 4 ++ [[], seed] } ==
  .error "layer 1 is not the successor of layer 0"
#guard check { evidence with layers := evidence.layers.dropLast } ==
  .error "wrong number of First-Crossing sector layers"
#guard check { evidence with metadata := { metadata with sectors := metadata.sectors.reverse } }
  == .error "First-Crossing sectors do not match canonical enumeration"
#guard check { evidence with metadata := { metadata with
    sectors := [⟨.low, 0, 0, 0⟩, ⟨.high 1 1 1, 1, 0, 0⟩] } } ==
  .error "First-Crossing sector bonus mismatch"

private def zero (p : Problem) (count : Nat) : FirstCrossingRun.Certificate :=
  ⟨⟨p, 0, count⟩, ⟨0, 0, 0, 1, []⟩, []⟩

#guard check (zero .closed 0) == .ok ⟨.closed, 0, 0⟩
#guard check (zero .open 1) == .ok ⟨.open, 0, 1⟩
#guard check { zero .open 1 with layers := [seed] } ==
  .error "wrong number of First-Crossing sector layers"
-- If source enumeration moves before the shape check, these guards cannot finish.
private def hugeMetadata : FirstCrossingRun.Metadata :=
  { metadata with nativeOrder := 1000000000, threshold := 1 }

#guard check { evidence with metadata := { hugeMetadata with sectors := [] }, layers := [] } ==
  .error "positive-order First-Crossing evidence must include sectors"
#guard check { evidence with metadata := hugeMetadata, layers := [] } ==
  .error "wrong number of First-Crossing sector layers"

private def parse := FirstCrossingSectorTable.parseLayer

#guard parse "" == .ok []
#guard parse "0,0,0,0| 1 0\n" == .ok seed
#guard parse "0,0,0,0|1,0 2 1\n" == .ok [(⟨⟨0, 0, 0, 0⟩, [1, 0]⟩, (2, 1))]
-- Whitespace, decimal spelling, pairing validity and numeric key order are exact.
#guard (["\n", "0,0,0,0| 1 0", "0,0,0,0| 1 0\r\n", "0,0,0,0| 1 0\n\n",
    " 0,0,0,0| 1 0\n", "0,0,0,0| 1 0 \n", "0,0,0,0|\t1 0\n", "0,0,0,0|  1 0\n",
    "0,0,0,0| 01 0\n", "00,0,0,0| 1 0\n", "0,0,0,0| 1 00\n", "0,0,0,0| 0 0\n",
    "0,0,0,0| -1 0\n", "0,0,0,0| 1 1e2\n", "0,0,0| 1 0\n", "0,0,0,0|| 1 0\n",
    "0,0,0,0|0 1 0\n", "0,0,0,0|2,0 1 0\n",
    "0,0,0,0| 1 0\n0,0,0,0| 2 1\n", "10,0,0,0| 1 0\n2,0,0,0| 1 0\n"] : List String).all
  (fun text => parse text matches .error _)
#guard (parse "2,0,0,0| 1 0\n10,0,0,0| 1 0\n") matches .ok _

end MeandersTests.FirstCrossingCertificates
