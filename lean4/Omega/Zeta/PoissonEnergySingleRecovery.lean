import Mathlib.Tactic

namespace Omega.Zeta

/-- Cleared-denominator single-defect Poisson identity.
    cor:xi-finite-defect-poisson-l2-energy-single-defect -/
theorem singleDefectEnergy_cleared
    (c δ : ℚ) :
    (c + δ) * c + (c - δ) * c - 2 * ((c - δ) * (c + δ)) = 2 * δ^2 := by
  ring

/-- `t+1` specialization of the cleared single-defect identity.
    cor:xi-finite-defect-poisson-l2-energy-single-defect -/
theorem singleDefectEnergy_cleared_t
    (t δ : ℚ) :
    ((t + 1 + δ) * (t + 1) + (t + 1 - δ) * (t + 1)
      - 2 * ((t + 1 - δ) * (t + 1 + δ))) = 2 * δ^2 := by
  ring

end Omega.Zeta
