import Omega.UnitCirclePhaseArithmetic.LeyangJoukowskyInverseSquare

namespace Omega.UnitCirclePhaseArithmetic

/-- The normalized dihedral Lee--Yang gate written in the `z^2`-coordinate. -/
noncomputable def leyangInverseSquareDihedralModel (z : ℂ) : ℂ :=
  -z ^ 2 / (1 + z ^ 2) ^ 2

/-- Paper label: `prop:leyang-inverse-square-dihedral-uniqueness`. -/
theorem paper_leyang_inverse_square_dihedral_uniqueness :
    leyangInverseSquareDihedralModel = fun z : ℂ => -(1 / (z + z⁻¹) ^ 2) := by
  funext z
  by_cases hz : z = 0
  · simp [leyangInverseSquareDihedralModel, hz]
  · simpa [leyangInverseSquareDihedralModel, one_div] using
      paper_leyang_jouwkowsky_inverse_square z hz

end Omega.UnitCirclePhaseArithmetic
