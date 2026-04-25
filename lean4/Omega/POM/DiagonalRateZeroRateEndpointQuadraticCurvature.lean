import Omega.POM.DiagonalRateDiagonalLogFeedback

namespace Omega.POM

noncomputable section

/-- Paper label: `thm:pom-diagonal-rate-zero-rate-endpoint-quadratic-curvature`. The diagonal
log-feedback identity identifies the first-order endpoint response, and the finite Pareto Legendre
package supplies the positive quadratic curvature of the endpoint law. -/
theorem paper_pom_diagonal_rate_zero_rate_endpoint_quadratic_curvature
    (D : PomFiniteParetoLegendreData)
    (Hw R delta Rp avgLogDiag kappa q : ℝ)
    (hkappa : kappa = Real.exp (-Rp) - 1)
    (hdiag : R = Hw + avgLogDiag - delta * Real.log (1 + kappa)) :
    R = Hw + avgLogDiag + delta * Rp ∧
      HasDerivAt D.pom_finite_pareto_legendre_curvature_slope
        (D.pom_finite_pareto_legendre_curvature_variance q) q ∧
      0 < D.pom_finite_pareto_legendre_curvature_variance q ∧
      D.pom_finite_pareto_legendre_curvature_legendreCurvature q =
        (D.pom_finite_pareto_legendre_curvature_variance q)⁻¹ ∧
      0 < D.pom_finite_pareto_legendre_curvature_legendreCurvature q := by
  have hfeedback :=
    paper_pom_diagonal_rate_diagonal_log_feedback D Hw R delta Rp avgLogDiag kappa q hkappa hdiag
  have hgeometry := paper_pom_finite_pareto_legendre_curvature D
  rcases hfeedback with ⟨hR, hslope, hvariance, _hmono⟩
  rcases hgeometry with ⟨_hfree, _hslope, _hvariance, _hmono, _hlegendre, hcurvature⟩
  refine ⟨hR, hslope, hvariance, hcurvature q, ?_⟩
  rw [hcurvature q]
  exact inv_pos.mpr hvariance

end

end Omega.POM
