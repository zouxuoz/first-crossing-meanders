import Meanders.Problems.Problem

/-!
# Known meander numbers

One table per problem, the Lean form of `fixtures/oeis/<tag>.txt`;
`scripts/policy.sh` checks that each pair agrees, and the Rust tests read
the text files, so every evaluator on either side is measured against the
same numbers. `known` indexes the tables by `Problem`.

These are data, not theorems: the theorem is that a counter computes
`Problem.number`, never that `Problem.number` is any particular number.
Jensen and Guttmann, "Critical exponents of plane meanders", J. Phys. A 33
(2000), L187–L192, Tables 1–3 (<https://arxiv.org/abs/cond-mat/0004321>;
DOI <https://doi.org/10.1088/0305-4470/33/21/101>), tabulate closed orders
through 24 and open crossings through 43. Their
arXiv tables disagree with the present OEIS data at closed 24 and open 43;
these entries are retained from OEIS, not attributed to those printed tables.
The later closed/open entries come from OEIS tables credited to Andrew Howroyd;
no primary publication or independently verified run for them is asserted here.

`agreesWithKnown` is the one-line check each algorithm's test file runs at
build time, once per problem it supports.
-/

namespace Meanders.Verification

/-- Closed meanders, OEIS A005315 (<https://oeis.org/A005315>), with the
project convention at order `0` (value `0`, unlike OEIS value `1`).
Positive orders through `28` are the OEIS b-file snapshot checked on 2026-09-08. -/
def closedMeanderNumbers : List (Nat × Nat) :=
  [(0, 0), (1, 1), (2, 2), (3, 8), (4, 42), (5, 262), (6, 1828), (7, 13820),
   (8, 110954), (9, 933458), (10, 8152860), (11, 73424650), (12, 678390116),
   (13, 6405031050), (14, 61606881612), (15, 602188541928), (16, 5969806669034),
   (17, 59923200729046), (18, 608188709574124), (19, 6234277838531806),
   (20, 64477712119584604), (21, 672265814872772972), (22, 7060941974458061392),
   (23, 74661728661167809752), (24, 794337831754570367812),
   (25, 8499066628515413229282), (26, 91412898898828176826244),
   (27, 987975910996038555989486), (28, 10726008363361842734385644)]

/-- Open meanders at genuine crossings `0` to `55`, the OEIS A005316
(<https://oeis.org/A005316>) b-file snapshot checked on 2026-09-08, credited
to Andrew Howroyd (first 44 terms from Iwan Jensen). -/
def openMeanderNumbers : List (Nat × Nat) :=
  [(0, 1), (1, 1), (2, 1), (3, 2), (4, 3), (5, 8), (6, 14), (7, 42), (8, 81), (9, 262), (10,
   538), (11, 1828), (12, 3926), (13, 13820), (14, 30694), (15, 110954), (16, 252939),
   (17, 933458), (18, 2172830), (19, 8152860), (20, 19304190), (21, 73424650),
   (22, 176343390), (23, 678390116), (24, 1649008456), (25, 6405031050),
   (26, 15730575554), (27, 61606881612), (28, 152663683494), (29, 602188541928),
   (30, 1503962954930), (31, 5969806669034), (32, 15012865733351),
   (33, 59923200729046), (34, 151622652413194), (35, 608188709574124),
   (36, 1547365078534578), (37, 6234277838531806), (38, 15939972379349178),
   (39, 64477712119584604), (40, 165597452660771610), (41, 672265814872772972),
   (42, 1733609081727968492), (43, 7060941974458061392), (44, 18276178714484582264),
   (45, 74661728661167809752), (46, 193909492888406631692),
   (47, 794337831754570367812), (48, 2069504277256274074724),
   (49, 8499066628515413229282), (50, 22206891674746169557410),
   (51, 91412898898828176826244), (52, 239489513356610743216954),
   (53, 987975910996038555989486), (54, 2594805632585289523975474),
   (55, 10726008363361842734385644)]

/-- The reference data for each problem, including the project zero conventions. -/
def known : Problem → List (Nat × Nat)
  | .closed => closedMeanderNumbers
  | .open => openMeanderNumbers

/-- `count` reproduces every tabulated reference value of `p` of order at most `upTo`. -/
def agreesWithKnown (p : Problem) (count : Nat → Nat) (upTo : Nat) : Bool :=
  (known p).all fun (n, c) => upTo < n || count n == c

end Meanders.Verification
