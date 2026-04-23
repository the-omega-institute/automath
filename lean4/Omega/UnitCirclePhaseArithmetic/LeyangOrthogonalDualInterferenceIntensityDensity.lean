import Omega.UnitCirclePhaseArithmetic.LeyangOrthogonalDualPushforwardDensityFormula

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The `ν₋` density from the orthogonal-dual interference model. -/
noncomputable def leyang_orthogonal_dual_interference_intensity_density_nu_minus_density
    (t : ℝ) : ℝ :=
  leyang_orthogonal_dual_pushforward_density_formula_density t

local notation "nu_minus_density" =>
  leyang_orthogonal_dual_interference_intensity_density_nu_minus_density

/-- Paper label: `cor:leyang-orthogonal-dual-interference-intensity-density`. -/
theorem paper_leyang_orthogonal_dual_interference_intensity_density
    (t : ℝ) (ht : 1 / 4 ≤ t) : nu_minus_density t = 1 / (Real.pi * t * Real.sqrt (4 * t - 1)) := by
  rw [leyang_orthogonal_dual_interference_intensity_density_nu_minus_density]
  rw [(paper_leyang_orthogonal_dual_pushforward_density_formula.2.2.2 t)]
  rw [if_pos ht]

end

end Omega.UnitCirclePhaseArithmetic
