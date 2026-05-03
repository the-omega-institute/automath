import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `cor:xi-toeplitz-negative-margin-from-hankel-fingerprint`. -/
theorem paper_xi_toeplitz_negative_margin_from_hankel_fingerprint
    (lambdaMin sigmaMin opNormR witnessNorm witnessRayleigh : Real)
    (hSigma : 0 ≤ sigmaMin)
    (hOp : 0 < opNormR)
    (hWitnessNorm : 0 < witnessNorm ∧ witnessNorm ≤ opNormR ^ 2)
    (hRayleigh : lambdaMin ≤ witnessRayleigh / witnessNorm)
    (hNegative : witnessRayleigh ≤ -sigmaMin ^ 2) :
    lambdaMin ≤ -sigmaMin ^ 2 / opNormR ^ 2 := by
  rcases hWitnessNorm with ⟨hWitnessNormPos, hWitnessNormLe⟩
  have hOpSqPos : 0 < opNormR ^ 2 := sq_pos_of_pos hOp
  have hNegDiv :
      witnessRayleigh / witnessNorm ≤ -sigmaMin ^ 2 / witnessNorm := by
    exact div_le_div_of_nonneg_right hNegative (le_of_lt hWitnessNormPos)
  have hDenom :
      -sigmaMin ^ 2 / witnessNorm ≤ -sigmaMin ^ 2 / opNormR ^ 2 := by
    rw [div_le_div_iff₀ hWitnessNormPos hOpSqPos]
    exact mul_le_mul_of_nonpos_left hWitnessNormLe (neg_nonpos.mpr (pow_nonneg hSigma 2))
  exact hRayleigh.trans (hNegDiv.trans hDenom)

end Omega.Zeta
