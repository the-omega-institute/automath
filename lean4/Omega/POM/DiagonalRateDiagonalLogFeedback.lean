import Omega.POM.DiagonalRateEulerDiagonalIdentity
import Omega.POM.FiniteParetoLegendreCurvature

namespace Omega.POM

noncomputable section

/-- Paper label: `prop:pom-diagonal-rate-diagonal-log-feedback`. The Euler diagonal identity
rewrites the logarithmic feedback term in closed form, while the finite Pareto escort model
supplies the derivative/variance identity and the resulting strict monotonicity of the diagonal
feedback slope. -/
theorem paper_pom_diagonal_rate_diagonal_log_feedback
    (D : PomFiniteParetoLegendreData)
    (Hw R delta Rp avgLogDiag kappa q : ℝ)
    (hkappa : kappa = Real.exp (-Rp) - 1)
    (hdiag : R = Hw + avgLogDiag - delta * Real.log (1 + kappa)) :
    R = Hw + avgLogDiag + delta * Rp ∧
      HasDerivAt D.pom_finite_pareto_legendre_curvature_slope
        (D.pom_finite_pareto_legendre_curvature_variance q) q ∧
      0 < D.pom_finite_pareto_legendre_curvature_variance q ∧
      StrictMono D.pom_finite_pareto_legendre_curvature_slope := by
  have hgeom := paper_pom_finite_pareto_legendre_curvature D
  rcases hgeom with ⟨_hfree, hslope, hvariance, hmono, _hlegendre, _hcurvature⟩
  refine ⟨paper_pom_diagonal_rate_euler_diagonal_identity Hw R delta Rp avgLogDiag kappa hkappa
    hdiag, hslope q, hvariance q, hmono⟩

end

end Omega.POM
