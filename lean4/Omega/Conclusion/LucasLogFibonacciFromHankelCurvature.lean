import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `cor:conclusion-lucas-log-fibonacci-from-hankel-curvature`. -/
theorem paper_conclusion_lucas_log_fibonacci_from_hankel_curvature (L logF : ℕ → ℝ)
    (hstep :
      ∀ q, 1 ≤ q → L q - L (q - 1) = 2 * (∑ d ∈ Finset.Icc 1 q, logF d)) :
    (∀ q, 1 ≤ q → L q - L (q - 1) = 2 * (∑ d ∈ Finset.Icc 1 q, logF d)) ∧
      (∀ q, 2 ≤ q →
        L q - 2 * L (q - 1) + L (q - 2) = 2 * logF q) ∧
        (∀ q, 2 ≤ q →
          logF q = (1 / 2 : ℝ) * (L q - 2 * L (q - 1) + L (q - 2))) := by
  refine ⟨hstep, ?_, ?_⟩
  · intro q hq
    have hq_one : 1 ≤ q := by omega
    have hqm1_one : 1 ≤ q - 1 := by omega
    have hsplit :
        (∑ d ∈ Finset.Icc 1 q, logF d) =
          (∑ d ∈ Finset.Icc 1 (q - 1), logF d) + logF q := by
      have htop :
          (∑ d ∈ Finset.Icc 1 ((q - 1) + 1), logF d) =
            (∑ d ∈ Finset.Icc 1 (q - 1), logF d) + logF ((q - 1) + 1) := by
        simpa using
          (Finset.sum_Icc_succ_top (f := logF) (show 1 ≤ q - 1 + 1 by omega))
      simpa [Nat.sub_add_cancel hq_one] using htop
    have hprev :
        L (q - 1) - L (q - 2) =
          2 * (∑ d ∈ Finset.Icc 1 (q - 1), logF d) := by
      simpa [show q - 1 - 1 = q - 2 by omega] using hstep (q - 1) hqm1_one
    have hdelta :
        (L q - L (q - 1)) - (L (q - 1) - L (q - 2)) = 2 * logF q := by
      rw [hstep q hq_one, hprev, hsplit]
      ring
    linarith
  · intro q hq
    have hsecond : L q - 2 * L (q - 1) + L (q - 2) = 2 * logF q := by
      have hq_one : 1 ≤ q := by omega
      have hqm1_one : 1 ≤ q - 1 := by omega
      have hsplit :
          (∑ d ∈ Finset.Icc 1 q, logF d) =
            (∑ d ∈ Finset.Icc 1 (q - 1), logF d) + logF q := by
        have htop :
            (∑ d ∈ Finset.Icc 1 ((q - 1) + 1), logF d) =
              (∑ d ∈ Finset.Icc 1 (q - 1), logF d) + logF ((q - 1) + 1) := by
          simpa using
            (Finset.sum_Icc_succ_top (f := logF) (show 1 ≤ q - 1 + 1 by omega))
        simpa [Nat.sub_add_cancel hq_one] using htop
      have hprev :
          L (q - 1) - L (q - 2) =
            2 * (∑ d ∈ Finset.Icc 1 (q - 1), logF d) := by
        simpa [show q - 1 - 1 = q - 2 by omega] using hstep (q - 1) hqm1_one
      have hdelta :
          (L q - L (q - 1)) - (L (q - 1) - L (q - 2)) = 2 * logF q := by
        rw [hstep q hq_one, hprev, hsplit]
        ring
      linarith
    linarith
