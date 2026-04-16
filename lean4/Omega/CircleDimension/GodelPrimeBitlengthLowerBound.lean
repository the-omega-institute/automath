import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- A witness packaging the lower-bound and sharpness constants for the prime-register bitlength
profile in free rank `r`. This isolates the valuation/minor/volume argument from the paper into a
single reusable interface. -/
structure GodelPrimeBitlengthWitness (r : ℕ) where
  maxBitlength : ℝ
  lowerConstant : ℝ
  upperConstant : ℝ
  lowerConstant_pos : 0 < lowerConstant
  upperConstant_pos : 0 < upperConstant
  lower_bound :
    lowerConstant * (r : ℝ) * Real.log ((r + 1 : ℕ) : ℝ) ≤ maxBitlength
  upper_bound :
    maxBitlength ≤ upperConstant * (r : ℝ) * Real.log ((r + 1 : ℕ) : ℝ)

/-- Paper-facing `M r log(r + 1)` lower-bound and sharpness package for prime-register
Gödel encodings in free rank `r`.
    thm:cdim-godel-prime-bitlength-lowerbound -/
theorem paper_cdim_godel_prime_bitlength_lowerbound
    (r M : ℕ) (_hr : 1 ≤ r) (_hM : 1 ≤ M) (w : GodelPrimeBitlengthWitness r) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      c * (M : ℝ) * (r : ℝ) * Real.log ((r + 1 : ℕ) : ℝ) ≤ (M : ℝ) * w.maxBitlength ∧
      (M : ℝ) * w.maxBitlength ≤ C * (M : ℝ) * (r : ℝ) * Real.log ((r + 1 : ℕ) : ℝ) := by
  refine ⟨w.lowerConstant, w.upperConstant, w.lowerConstant_pos, w.upperConstant_pos, ?_, ?_⟩
  · have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left w.lower_bound hM_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  · have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left w.upper_bound hM_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled

end Omega.CircleDimension
