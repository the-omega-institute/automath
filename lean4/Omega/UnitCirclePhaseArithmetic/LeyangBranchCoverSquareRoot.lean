import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Real-valued Lee--Yang branch-cover profile on the unit circle in the angular coordinate. -/
noncomputable def leyangBranchCover (θ : ℝ) : ℝ :=
  -(1 / (4 * Real.cos θ ^ 2))

/-- The local square-root uniformizing coordinate at the endpoint `-1 / 4`. -/
noncomputable def leyangBranchUniformizer (θ : ℝ) : ℝ :=
  Real.tan θ / 2

/-- Explicit derivative of the branch-cover profile away from the quarter-turn singularities. -/
noncomputable def leyangBranchCoverDerivative (θ : ℝ) : ℝ :=
  -(Real.sin θ / (2 * Real.cos θ ^ 3))

/-- Along the singular Lee--Yang ray, the angular branch cover is given by the explicit
`-1 / (4 cos^2 θ)` formula, the usual four angular representatives have the same value, the
derivative is nonzero away from the excluded points, and the endpoint `-1 / 4` admits the exact
square-root uniformization `-(tan θ / 2)^2`. `thm:leyang-branch-cover-square-root` -/
theorem paper_leyang_branch_cover_square_root (θ : ℝ)
    (hsin : Real.sin θ ≠ 0) (hcos : Real.cos θ ≠ 0) :
    leyangBranchCover θ = -(1 / (4 * Real.cos θ ^ 2)) ∧
      leyangBranchCover (-θ) = leyangBranchCover θ ∧
      leyangBranchCover (Real.pi - θ) = leyangBranchCover θ ∧
      leyangBranchCover (θ + Real.pi) = leyangBranchCover θ ∧
      leyangBranchCoverDerivative θ ≠ 0 ∧
      leyangBranchCover 0 = (-(1 / 4 : ℝ)) ∧
      leyangBranchCover θ + (1 / 4 : ℝ) = -(leyangBranchUniformizer θ ^ 2) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [leyangBranchCover, Real.cos_neg]
  · simp [leyangBranchCover, Real.cos_pi_sub]
  · simp [leyangBranchCover, Real.cos_add_pi]
  · unfold leyangBranchCoverDerivative
    exact neg_ne_zero.mpr <|
      div_ne_zero hsin
        (mul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) (pow_ne_zero 3 hcos))
  · simp [leyangBranchCover]
  · have htrig : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := by
      simpa [pow_two] using Real.sin_sq_add_cos_sq θ
    calc
      leyangBranchCover θ + (1 / 4 : ℝ) = (Real.cos θ ^ 2 - 1) / (4 * Real.cos θ ^ 2) := by
        unfold leyangBranchCover
        field_simp [hcos]
        ring_nf
      _ = -(Real.sin θ ^ 2 / (4 * Real.cos θ ^ 2)) := by
        have hrewrite : Real.cos θ ^ 2 - 1 = -Real.sin θ ^ 2 := by
          nlinarith
        rw [hrewrite]
        ring
      _ = -(leyangBranchUniformizer θ ^ 2) := by
        unfold leyangBranchUniformizer
        rw [Real.tan_eq_sin_div_cos]
        field_simp [hcos]
        ring

end Omega.UnitCirclePhaseArithmetic
