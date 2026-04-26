import Omega.POM.FiniteParetoLegendreCurvature

namespace Omega.POM

noncomputable section

/-- Concrete diagonal-rate statement extracted from the two-point escort/Pareto model: the
free energy is differentiable with slope equal to the optimal parameter curve, the slope
derivative is the Bernoulli variance, the slope is strictly monotone, and the curvature is the
reciprocal variance. -/
def pom_diagonal_rate_analytic_strict_convexity_curvature_statement : Prop :=
  ∀ D : PomFiniteParetoLegendreData,
    (∀ q,
      HasDerivAt D.pom_finite_pareto_legendre_curvature_freeEnergy
        (D.pom_finite_pareto_legendre_curvature_slope q) q) ∧
      (∀ q,
        HasDerivAt D.pom_finite_pareto_legendre_curvature_slope
          (D.pom_finite_pareto_legendre_curvature_variance q) q) ∧
      StrictMono D.pom_finite_pareto_legendre_curvature_slope ∧
      (∀ q, 0 < D.pom_finite_pareto_legendre_curvature_variance q) ∧
      (∀ q,
        D.pom_finite_pareto_legendre_curvature_legendreCurvature q =
          (D.pom_finite_pareto_legendre_curvature_variance q)⁻¹)

/-- Paper label: `prop:pom-diagonal-rate-analytic-strict-convexity-curvature`. -/
theorem paper_pom_diagonal_rate_analytic_strict_convexity_curvature :
    pom_diagonal_rate_analytic_strict_convexity_curvature_statement := by
  intro D
  rcases paper_pom_finite_pareto_legendre_curvature D with
    ⟨hfree, hslope, hvar_pos, hslope_strict, _hpoint, hcurv⟩
  exact ⟨hfree, hslope, hslope_strict, hvar_pos, hcurv⟩

end

end Omega.POM
