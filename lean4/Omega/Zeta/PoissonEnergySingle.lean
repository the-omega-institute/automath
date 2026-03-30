import Mathlib.Tactic

namespace Omega.Zeta

/-- Single-defect Poisson `L²` energy rational identity.
    cor:xi-finite-defect-poisson-l2-energy-single-defect -/
theorem singleDefectEnergy_rational_identity (t δ : ℚ) :
    (1 / (2 * (t + 1 - δ)) + 1 / (2 * (t + 1 + δ)) - 1 / (t + 1))
      = δ^2 / ((t + 1) * ((t + 1)^2 - δ^2)) := by
  field_simp
  ring

/-- Nonnegativity of the quadratic numerator.
    cor:xi-finite-defect-poisson-l2-energy-single-defect -/
theorem singleDefectEnergy_nonneg_num (t δ : ℚ) :
    0 ≤ δ^2 := by
  nlinarith

end Omega.Zeta
