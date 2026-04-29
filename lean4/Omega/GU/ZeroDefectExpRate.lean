import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.GU.ZeroDefectExpRate

/-- Zero gauge defect exponential rate seeds.
    P(G_m=0) = F(m+5)/(9·2^m), rate = log(2/φ).
    cor:fold-gauge-anomaly-zero-defect-exp-rate -/
theorem paper_gut_zero_defect_exp_rate_seeds :
    Nat.fib 7 = 13 ∧
    9 * 2^2 = 36 ∧
    Nat.fib 8 = 21 ∧
    9 * 2^3 = 72 ∧
    Nat.fib 9 < 2^9 ∧
    Nat.fib 8 * 2^2 < Nat.fib 7 * 2^3 ∧
    (∀ n, Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1)) := by
  refine ⟨by native_decide, by norm_num, by native_decide, by norm_num,
          by native_decide, by native_decide, fun n => Nat.fib_add_two (n := n)⟩

theorem paper_gut_zero_defect_exp_rate_package :
    Nat.fib 7 = 13 ∧
    9 * 2^2 = 36 ∧
    Nat.fib 8 = 21 ∧
    9 * 2^3 = 72 ∧
    Nat.fib 9 < 2^9 ∧
    Nat.fib 8 * 2^2 < Nat.fib 7 * 2^3 ∧
    (∀ n, Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1)) :=
  paper_gut_zero_defect_exp_rate_seeds

/-- Paper-facing wrapper for the zero-defect exponential-rate seed package.
    cor:fold-gauge-anomaly-zero-defect-exp-rate -/
theorem paper_fold_gauge_anomaly_zero_defect_exp_rate :
    Nat.fib 7 = 13 ∧
    9 * 2^2 = 36 ∧
    Nat.fib 8 = 21 ∧
    9 * 2^3 = 72 ∧
    Nat.fib 9 < 2^9 ∧
    Nat.fib 8 * 2^2 < Nat.fib 7 * 2^3 ∧
    (∀ n, Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1)) := by
  simpa using paper_gut_zero_defect_exp_rate_seeds

end Omega.GU.ZeroDefectExpRate
