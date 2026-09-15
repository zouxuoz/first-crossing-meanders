import Meanders.Certify.FirstCrossing.Replay

namespace Meanders.Certified

private def certificate : Certify.FirstCrossingRun.Certificate :=
{ claim := { problem := Meanders.Problem.open, n := 4, count := 3 },
  metadata := { nativeOrder := 2,
                threshold := 2,
                closed := 2,
                openEven := 3,
                sectors := [{ sector := Meanders.FirstCrossing.Sector.low,
                              ordinary := 2,
                              lowerReturns := 3,
                              bonusContribution := 0 },
                            { sector := Meanders.FirstCrossing.Sector.high 2 2 2,
                              ordinary := 0,
                              lowerReturns := 0,
                              bonusContribution := 0 }] },
  layers := [[({ counters := { pl := 0, pr := 0, ql := 0, qr := 0 }, mate := [] }, 1, 0)],
             [({ counters := { pl := 0, pr := 0, ql := 0, qr := 0 }, mate := [1, 0] }, 1, 0)],
             [({ counters := { pl := 0, pr := 0, ql := 1, qr := 0 }, mate := [1, 0] }, 1, 1),
              ({ counters := { pl := 1, pr := 0, ql := 0, qr := 0 }, mate := [1, 0] }, 1, 0)],
             [({ counters := { pl := 1, pr := 0, ql := 1, qr := 0 }, mate := [1, 0] }, 2, 1)],
             [({ counters := { pl := 2, pr := 0, ql := 2, qr := 0 }, mate := [] }, 2, 3)],
             [({ counters := { pl := 0, pr := 0, ql := 0, qr := 0 }, mate := [] }, 1, 0)],
             [({ counters := { pl := 0, pr := 0, ql := 0, qr := 0 }, mate := [1, 0] }, 1, 0)],
             [],
             [],
             []] }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Explicit sector evidence needs a larger local kernel reduction budget.
/-- A concrete open count from exact sector evidence, kernel replayed. -/
theorem first_crossing_open_n4 : openMeanderNumber 4 = 3 :=
  (Certify.FirstCrossingRun.Certificate.replayClaim?_sound
    (c := certificate) (claim := certificate.claim) (by decide +kernel)).symm

end Meanders.Certified
