import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The conformal factor of stereographic coordinates, recorded as a scalar density model in the
single radial variable `xNormSq = ‖x‖^2`. -/
noncomputable def stereographicConformalFactor (xNormSq : ℝ) : ℝ :=
  2 / (1 + xNormSq)

/-- The pullback density of the Euclidean volume form under stereographic coordinates. -/
noncomputable def stereographicPullbackVolumeDensity (n : ℕ) (xNormSq : ℝ) : ℝ :=
  stereographicConformalFactor xNormSq ^ n

/-- Paper label: `prop:stereographic-volume-form`. The stereographic pullback density is the
`n`-th power of the conformal factor `2 / (1 + ‖x‖^2)`. -/
theorem paper_stereographic_volume_form (n : ℕ) (xNormSq : ℝ) :
    stereographicPullbackVolumeDensity n xNormSq = (2 : ℝ) ^ n / (1 + xNormSq) ^ n := by
  simp [stereographicPullbackVolumeDensity, stereographicConformalFactor, div_pow]

end

end Omega.UnitCirclePhaseArithmetic
