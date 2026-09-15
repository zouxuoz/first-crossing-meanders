import Meanders.Models.FirstCrossing.Native.Eval
import Meanders.Models.FirstCrossing.Correctness.JointCorrect

/-! First-Crossing correctness through the actual native/source bijection. -/
namespace Meanders.FirstCrossing

/-- The shared First-Crossing reference computes the unchanged public Closed/Open problems. -/
theorem count_eq (p : Problem) (n : ℕ) :
    count p n = p.number n := by
  cases p with
  | closed => exact (evaluate_correct n).1
  | «open» =>
    change (if n = 0 then 1 else if n % 2 = 1 then (evaluate (n / 2 + 1)).closed
      else (evaluate (n / 2)).openEven) = openMeanderNumber n
    split_ifs with hz ho
    · subst n
      exact openMeanderNumber_zero.symm
    · rw [(evaluate_correct (n / 2 + 1)).1, ← openMeanderNumber_odd]
      congr 1
      omega
    · rw [(evaluate_correct (n / 2)).2]
      congr 1
      omega

end Meanders.FirstCrossing
