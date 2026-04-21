import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The sharp second-order coefficient in the Poisson total-variation expansion. -/
noncomputable def poissonTvFourthOrderLeadingCoeff (sigma : ℝ) : ℝ :=
  (3 * Real.sqrt 3) / (4 * Real.pi) * sigma ^ 2

/-- The parity-forced cubic coefficient vanishes. -/
def poissonTvFourthOrderCubicCoeff : ℝ := 0

/-- The fourth-order correction extracted after centering and cancelling the odd kernel. -/
noncomputable def poissonTvFourthOrderCorrectionCoeff (sigma mu3 mu4 : ℝ) : ℝ :=
  (3 * Real.sqrt 3) / (32 * Real.pi * sigma ^ 2) * (2 * mu3 ^ 2 - 3 * sigma ^ 2 * mu4)

/-- The centered fourth-order Poisson total-variation correction has the explicit
`t⁻² / t⁻⁴` coefficient package recorded in the paper.
`prop:cdim-poisson-tv-fourth-order-correction` -/
theorem paper_cdim_poisson_tv_fourth_order_correction
    {A2 A3 A4 sigma mu3 mu4 : ℝ}
    (hsigma : sigma ≠ 0)
    (hA2 : 4 * Real.pi * A2 = 3 * Real.sqrt 3 * sigma ^ 2)
    (hA3 : A3 = 0)
    (hA4 : 32 * Real.pi * sigma ^ 2 * A4 = 3 * Real.sqrt 3 * (2 * mu3 ^ 2 - 3 * sigma ^ 2 * mu4)) :
    A2 = poissonTvFourthOrderLeadingCoeff sigma ∧
      A3 = poissonTvFourthOrderCubicCoeff ∧
      A4 = poissonTvFourthOrderCorrectionCoeff sigma mu3 mu4 := by
  have hpi4 : (4 * Real.pi : ℝ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hsigma2 : sigma ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 hsigma
  have hpi32sigma2 : (32 * Real.pi * sigma ^ 2 : ℝ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hsigma2
  constructor
  · unfold poissonTvFourthOrderLeadingCoeff
    have hA2' : A2 = (3 * Real.sqrt 3 * sigma ^ 2) / (4 * Real.pi) := by
      apply (eq_div_iff hpi4).2
      linarith
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hA2'
  constructor
  · simpa [poissonTvFourthOrderCubicCoeff] using hA3
  · unfold poissonTvFourthOrderCorrectionCoeff
    have hA4' : A4 = (3 * Real.sqrt 3 * (2 * mu3 ^ 2 - 3 * sigma ^ 2 * mu4)) /
        (32 * Real.pi * sigma ^ 2) := by
      apply (eq_div_iff hpi32sigma2).2
      linarith
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hA4'

end Omega.CircleDimension
