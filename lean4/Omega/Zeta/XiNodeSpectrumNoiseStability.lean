import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-node-spectrum-noise-stability`. -/
theorem paper_xi_node_spectrum_noise_stability
    {matrixGap spectralGap logGap h0inv h1err h0err opNorm kappa r : ℝ}
    (hr : 0 < r)
    (hkappa : 0 ≤ kappa)
    (hmatrix : matrixGap ≤ 4 * h0inv * (h1err + opNorm * h0err))
    (hspectral : spectralGap ≤ kappa * matrixGap)
    (hlog : logGap ≤ (2 / r) * spectralGap) :
    logGap ≤ (2 / r) * (kappa * (4 * h0inv * (h1err + opNorm * h0err))) := by
  have hcoef : 0 ≤ (2 / r : ℝ) := by positivity
  calc
    logGap ≤ (2 / r) * spectralGap := hlog
    _ ≤ (2 / r) * (kappa * matrixGap) :=
      mul_le_mul_of_nonneg_left hspectral hcoef
    _ ≤ (2 / r) * (kappa * (4 * h0inv * (h1err + opNorm * h0err))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmatrix hkappa) hcoef

end Omega.Zeta
