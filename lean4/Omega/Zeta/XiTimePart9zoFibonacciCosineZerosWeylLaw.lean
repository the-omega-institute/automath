import Mathlib
import Omega.Zeta.XiFoldResonanceZeroCountSelfsimilarLinear

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zo-fibonacci-cosine-zeros-weyl-law`.

The positive Fibonacci-cosine zero count is modeled by the existing fold-resonance floor sum. The
index-shift identity yields the one-step self-similar recurrence for the truncated sum, and the
already formalized floor-error estimate gives the corresponding linear counting bound. -/
theorem paper_xi_time_part9zo_fibonacci_cosine_zeros_weyl_law
    (R : ℝ) (hR : 0 < R) :
    foldResonancePositiveZeroCount R =
      foldResonanceScaleTerm R 0 +
        foldResonancePositiveZeroCountAux (R / Real.goldenRatio) (Nat.floor R) ∧
      ((foldResonancePositiveZeroCount R : ℝ) ≤
        foldResonanceLinearMainTerm R (Nat.floor R + 1) + (Nat.floor R + 1)) ∧
      ((2 * foldResonancePositiveZeroCount R : ℝ) ≤
        2 * foldResonanceLinearMainTerm R (Nat.floor R + 1) + 2 * (Nat.floor R + 1)) := by
  obtain ⟨hcount, hshift, hupper⟩ := paper_xi_fold_resonance_zero_count_selfsimilar_linear R hR
  refine ⟨?_, hupper, ?_⟩
  · rw [hcount, foldResonancePositiveZeroCountAux, Finset.sum_range_succ']
    simp [foldResonancePositiveZeroCountAux, hshift, add_comm]
  · have hdouble :
        (2 : ℝ) * (foldResonancePositiveZeroCount R : ℝ) ≤
          (2 : ℝ) * (foldResonanceLinearMainTerm R (Nat.floor R + 1) + (Nat.floor R + 1)) := by
      exact mul_le_mul_of_nonneg_left hupper (by positivity)
    simpa [two_mul, mul_add, add_assoc, add_left_comm, add_comm] using hdouble

end Omega.Zeta
