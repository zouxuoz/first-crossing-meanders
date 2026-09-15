import Meanders.Certify.FirstCrossing.Replay

namespace Meanders.Certified

private def certificate : Certify.FirstCrossingRun.Certificate :=
{ claim := { problem := Meanders.Problem.open, n := 2, count := 1 },
  metadata := { nativeOrder := 1,
                threshold := 1,
                closed := 1,
                openEven := 1,
                sectors := [{ sector := Meanders.FirstCrossing.Sector.low,
                              ordinary := 0,
                              lowerReturns := 0,
                              bonusContribution := 0 },
                            { sector := Meanders.FirstCrossing.Sector.high 1 1 1,
                              ordinary := 1,
                              lowerReturns := 0,
                              bonusContribution := 1 }] },
  layers := [[({ counters := { pl := 0, pr := 0, ql := 0, qr := 0 }, mate := [] }, 1, 0)],
             [],
             [],
             [({ counters := { pl := 0, pr := 0, ql := 0, qr := 0 }, mate := [] }, 1, 0)],
             [({ counters := { pl := 0, pr := 0, ql := 0, qr := 0 }, mate := [1, 0] }, 1, 0)],
             [({ counters := { pl := 0, pr := 0, ql := 0, qr := 0 }, mate := [] }, 1, 0)]] }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Explicit sector evidence needs a larger local kernel reduction budget.
/-- A concrete open count from exact sector evidence, kernel replayed. -/
theorem first_crossing_open_n2 : openMeanderNumber 2 = 1 :=
  (Certify.FirstCrossingRun.Certificate.replayClaim?_sound
    (c := certificate) (claim := certificate.claim) (by decide +kernel)).symm

end Meanders.Certified
