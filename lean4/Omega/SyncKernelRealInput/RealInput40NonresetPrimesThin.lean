import Mathlib
import Omega.SyncKernelRealInput.RealInputDefectEntropy

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The audited `10`-to-`1` lift factor from nonreset primitive loops in the `40`-state kernel to
primitive loops in the defect subshift. -/
def real_input_40_nonreset_primes_thin_lift_factor : ℝ := 10

/-- The Perron-root proxy reused from the defect-entropy package. -/
def real_input_40_nonreset_primes_thin_alpha (m : ℕ) : ℝ :=
  real_input_defect_entropy_perron_root m

/-- Concrete bookkeeping for the nonreset-prime thinness estimate. -/
structure RealInput40NonresetPrimesThinData where
  defectLevel : ℕ
  growthConstant : ℝ
  defectPrimitiveCount : ℕ → ℝ
  defectOrbitCount : ℕ → ℝ
  noresetPrimeCount : ℕ → ℝ
  kernelLiftBound :
    ∀ n : ℕ, noresetPrimeCount n ≤
      real_input_40_nonreset_primes_thin_lift_factor * defectPrimitiveCount n
  defectDivisorInequality :
    ∀ n : ℕ, 1 ≤ n → (n : ℝ) * defectPrimitiveCount n ≤ defectOrbitCount n
  defectPerronGrowth :
    ∀ n : ℕ, defectOrbitCount n ≤
      growthConstant * real_input_40_nonreset_primes_thin_alpha defectLevel ^ n

/-- The effective constant after absorbing the `10`-to-`1` lift factor into the defect growth
constant. -/
def real_input_40_nonreset_primes_thin_effective_constant
    (D : RealInput40NonresetPrimesThinData) : ℝ :=
  real_input_40_nonreset_primes_thin_lift_factor * D.growthConstant

namespace RealInput40NonresetPrimesThinData

/-- Concrete paper-facing thinness statement: the nonreset primitive count is bounded by
`C_m α_m^n / n`. -/
def Holds (D : RealInput40NonresetPrimesThinData) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    D.noresetPrimeCount n ≤
      real_input_40_nonreset_primes_thin_effective_constant D *
        real_input_40_nonreset_primes_thin_alpha D.defectLevel ^ n / n

end RealInput40NonresetPrimesThinData

/-- Paper label: `thm:real-input-40-nonreset-primes-thin`.
The `10`-to-`1` kernel lift bound, combined with the defect-subshift growth
`a_n(R_m) = O(α_m^n)` and the standard divisor inequality `a_n ≥ n p_n`, yields the thinness
estimate `p_n^noreset ≤ C_m α_m^n / n`. -/
theorem paper_real_input_40_nonreset_primes_thin (D : RealInput40NonresetPrimesThinData) :
    D.Holds := by
  intro n hn
  have hn_real_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hlift_nonneg : 0 ≤ real_input_40_nonreset_primes_thin_lift_factor := by
    norm_num [real_input_40_nonreset_primes_thin_lift_factor]
  have hdefectPrimitive :
      D.defectPrimitiveCount n ≤ D.defectOrbitCount n / n := by
    have hdivisor :
        D.defectPrimitiveCount n * (n : ℝ) ≤ D.defectOrbitCount n := by
      simpa [mul_comm] using D.defectDivisorInequality n hn
    exact (le_div_iff₀ hn_real_pos).2 hdivisor
  calc
    D.noresetPrimeCount n
        ≤ real_input_40_nonreset_primes_thin_lift_factor * D.defectPrimitiveCount n :=
      D.kernelLiftBound n
    _ ≤ real_input_40_nonreset_primes_thin_lift_factor * (D.defectOrbitCount n / n) := by
      exact mul_le_mul_of_nonneg_left hdefectPrimitive hlift_nonneg
    _ ≤ real_input_40_nonreset_primes_thin_lift_factor *
          (D.growthConstant * real_input_40_nonreset_primes_thin_alpha D.defectLevel ^ n / n) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (D.defectPerronGrowth n) hn_real_pos.le) hlift_nonneg
    _ = real_input_40_nonreset_primes_thin_effective_constant D *
          real_input_40_nonreset_primes_thin_alpha D.defectLevel ^ n / n := by
      unfold real_input_40_nonreset_primes_thin_effective_constant
      ring

end
end Omega.SyncKernelRealInput
