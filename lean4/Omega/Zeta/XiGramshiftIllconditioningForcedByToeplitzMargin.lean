import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.XiToeplitzNegativeMarginVandermonde4Lowerbound

namespace Omega.Zeta

open XiToeplitzNegativeMarginData

/-- The first Toeplitz negative-margin lower bound forces the Gram inverse scale to diverge at
least like the reciprocal margin once the singular value and conjugation norm are positive.
    prop:xi-gramshift-illconditioning-forced-by-toeplitz-margin -/
theorem paper_xi_gramshift_illconditioning_forced_by_toeplitz_margin
    (D : XiToeplitzNegativeMarginData) (hσ : 0 < D.sigmaMin) (hR : 0 < D.opNormR) :
    (D.opNormR ^ 2 * D.delta)⁻¹ ≤ (D.sigmaMin ^ 2)⁻¹ := by
  have hmargin := (paper_xi_toeplitz_negative_margin_vandermonde4_lowerbound D).1
  have hσ2 : 0 < D.sigmaMin ^ 2 := sq_pos_of_pos hσ
  have hR2 : 0 < D.opNormR ^ 2 := sq_pos_of_pos hR
  have hmul : D.sigmaMin ^ 2 ≤ D.delta * D.opNormR ^ 2 := by
    exact (div_le_iff₀ hR2).1 hmargin
  have hmul' : D.sigmaMin ^ 2 ≤ D.opNormR ^ 2 * D.delta := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  simpa [one_div] using one_div_le_one_div_of_le hσ2 hmul'

end Omega.Zeta
