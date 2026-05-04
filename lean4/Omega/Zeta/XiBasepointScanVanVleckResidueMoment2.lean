import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete coefficient package for the second residue moment calculation.  The first balance is
the `z^-3` coefficient comparison, and the second is the normalized sign convention for
`r_k = -y'/y`. -/
structure xi_basepoint_scan_van_vleck_residue_moment2_data where
  b0 : ℝ
  b1 : ℝ
  A1 : ℝ
  secondResidueMoment : ℝ
  yDerivativeMoment : ℝ
  kappa : ℝ
  gammaSum : ℝ
  xSum : ℝ
  coefficientBalance : b1 = 2 * secondResidueMoment + b0 * A1
  logarithmicDerivativeBalance : yDerivativeMoment = -(-kappa * gammaSum - xSum)

/-- Paper label: `prop:xi-basepoint-scan-van-vleck-residue-moment2`. -/
theorem paper_xi_basepoint_scan_van_vleck_residue_moment2
    (D : xi_basepoint_scan_van_vleck_residue_moment2_data) :
    D.secondResidueMoment = (D.b1 - D.b0 * D.A1) / 2 ∧
      D.yDerivativeMoment = D.kappa * D.gammaSum + D.xSum := by
  constructor
  · linarith [D.coefficientBalance]
  · rw [D.logarithmicDerivativeBalance]
    ring

end Omega.Zeta
