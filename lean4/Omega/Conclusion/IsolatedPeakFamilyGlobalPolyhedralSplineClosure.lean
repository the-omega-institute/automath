import Omega.Conclusion.IntegerSupportedCurvatureExactSplineReconstruction

namespace Omega.Conclusion

/-- Concrete isolated-peak family data.  The isolated peak parameters select the tail family, while
the reconstruction package supplies the integer-supported curvature spline recovered from it. -/
structure conclusion_isolated_peak_family_global_polyhedral_spline_closure_data where
  conclusion_isolated_peak_family_global_polyhedral_spline_closure_reconstruction :
    conclusion_integer_supported_curvature_exact_spline_reconstruction_data
  conclusion_isolated_peak_family_global_polyhedral_spline_closure_peakCenter : ℕ
  conclusion_isolated_peak_family_global_polyhedral_spline_closure_peakHeight : ℝ

namespace conclusion_isolated_peak_family_global_polyhedral_spline_closure_data

/-- The curvature coefficients in the tail are recovered from integer-indexed fan widths. -/
def tailSupportInteger
    (D : conclusion_isolated_peak_family_global_polyhedral_spline_closure_data) : Prop :=
  conclusion_integer_supported_curvature_exact_spline_reconstruction_data.coefficientsRecovered
    D.conclusion_isolated_peak_family_global_polyhedral_spline_closure_reconstruction

/-- The tail pressure curve lies in the anchored polyhedral spline closure. -/
def tailSplineClosure
    (D : conclusion_isolated_peak_family_global_polyhedral_spline_closure_data) : Prop :=
  conclusion_integer_supported_curvature_exact_spline_reconstruction_data.splineReconstructsPressure
    D.conclusion_isolated_peak_family_global_polyhedral_spline_closure_reconstruction

end conclusion_isolated_peak_family_global_polyhedral_spline_closure_data

/-- Paper label:
`cor:conclusion-isolated-peak-family-global-polyhedral-spline-closure`. -/
theorem paper_conclusion_isolated_peak_family_global_polyhedral_spline_closure
    (D : conclusion_isolated_peak_family_global_polyhedral_spline_closure_data) :
    D.tailSupportInteger ∧ D.tailSplineClosure := by
  have h :=
    paper_conclusion_integer_supported_curvature_exact_spline_reconstruction
      D.conclusion_isolated_peak_family_global_polyhedral_spline_closure_reconstruction
  exact ⟨h.1, h.2.1⟩

end Omega.Conclusion
