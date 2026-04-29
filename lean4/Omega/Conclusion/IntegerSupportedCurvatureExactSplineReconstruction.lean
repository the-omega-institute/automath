import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Concrete data for the integer-supported curvature reconstruction.  The functions record the
discrete fan widths, the recovered curvature coefficients, the pressure curve, the endpoint
anchors, and the integer-supported curvature contribution to the spline formula. -/
structure conclusion_integer_supported_curvature_exact_spline_reconstruction_data where
  fanWidth : ℕ → ℝ
  curvatureCoefficient : ℕ → ℝ
  pressure : ℝ → ℝ
  anchor0 : ℝ
  anchor1 : ℝ
  curvatureContribution : ℝ → ℝ
  coefficientRecovery : ∀ n : ℕ, curvatureCoefficient n = fanWidth (n + 1)
  splineFormula :
    ∀ t : ℝ, pressure t = anchor0 + (anchor1 - anchor0) * t + curvatureContribution t

namespace conclusion_integer_supported_curvature_exact_spline_reconstruction_data

/-- The pressure spline determined by the two anchors and the integer curvature contribution. -/
def spline (D : conclusion_integer_supported_curvature_exact_spline_reconstruction_data)
    (t : ℝ) : ℝ :=
  D.anchor0 + (D.anchor1 - D.anchor0) * t + D.curvatureContribution t

/-- Coefficient recovery from the discrete fan widths. -/
def coefficientsRecovered
    (D : conclusion_integer_supported_curvature_exact_spline_reconstruction_data) : Prop :=
  ∀ n : ℕ, D.curvatureCoefficient n = D.fanWidth (n + 1)

/-- Exact reconstruction of the pressure curve by the anchored spline formula. -/
def splineReconstructsPressure
    (D : conclusion_integer_supported_curvature_exact_spline_reconstruction_data) : Prop :=
  ∀ t : ℝ, D.pressure t = D.spline t

/-- Uniqueness among curves satisfying the same anchored spline formula. -/
def uniqueDetermination
    (D : conclusion_integer_supported_curvature_exact_spline_reconstruction_data) : Prop :=
  ∀ pressure' : ℝ → ℝ, (∀ t : ℝ, pressure' t = D.spline t) → pressure' = D.pressure

end conclusion_integer_supported_curvature_exact_spline_reconstruction_data

/-- Paper label: `thm:conclusion-integer-supported-curvature-exact-spline-reconstruction`. -/
theorem paper_conclusion_integer_supported_curvature_exact_spline_reconstruction
    (D : conclusion_integer_supported_curvature_exact_spline_reconstruction_data) :
    D.coefficientsRecovered ∧ D.splineReconstructsPressure ∧ D.uniqueDetermination := by
  refine ⟨D.coefficientRecovery, ?_, ?_⟩
  · intro t
    simpa [conclusion_integer_supported_curvature_exact_spline_reconstruction_data.spline]
      using D.splineFormula t
  · intro pressure' hpressure'
    funext t
    rw [hpressure' t]
    symm
    simpa [conclusion_integer_supported_curvature_exact_spline_reconstruction_data.spline]
      using D.splineFormula t

end Omega.Conclusion
