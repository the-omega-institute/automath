import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Zeta

/-- The leading `e^{-θ/2}` contribution to `1/2 - P'(θ)`. -/
noncomputable def zeroTempSlopeDefectLeading (c d : ℝ) (θ : ℝ) : ℝ :=
  (d / (2 * c)) * Real.exp (-θ / 2)

/-- The leading `e^{-θ/2}` contribution to `P''(θ)`. -/
noncomputable def zeroTempCurvatureLeading (c d : ℝ) (θ : ℝ) : ℝ :=
  (d / (4 * c)) * Real.exp (-θ / 2)

/-- For the zero-temperature square-root branch, the leading slope defect and curvature have the
same `u^{-1/2}` scale, and their quotient is the universal constant `2`.
    thm:xi-output-potential-zero-temp-square-root-critical-law -/
theorem paper_xi_output_potential_zero_temp_square_root_critical_law
    (c d θ u : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) (hu : u = Real.exp θ) :
    zeroTempSlopeDefectLeading c d θ / zeroTempCurvatureLeading c d θ = 2 ∧
    zeroTempSlopeDefectLeading c d θ = (d / (2 * c)) * u ^ (-(1 / 2 : ℝ)) ∧
    zeroTempCurvatureLeading c d θ = (d / (4 * c)) * u ^ (-(1 / 2 : ℝ)) := by
  have hexp : Real.exp (-θ / 2) ≠ 0 := by positivity
  have huhalf : u ^ (-(1 / 2 : ℝ)) = Real.exp (-θ / 2) := by
    rw [hu]
    rw [show -θ / 2 = θ * (-(1 / 2 : ℝ)) by ring]
    rw [Real.exp_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold zeroTempSlopeDefectLeading zeroTempCurvatureLeading
    field_simp [hc, hd, hexp]
    ring
  · unfold zeroTempSlopeDefectLeading
    rw [huhalf]
  · unfold zeroTempCurvatureLeading
    rw [huhalf]

end Omega.Zeta
