import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyMean

namespace Omega.POM

/-- A rewrite strategy is encoded by the expected rewrite-step density `m ↦ E[T_{m+1}] / m`,
subject to the pointwise comparison with the already formalized gauge-anomaly mean density. -/
abbrev cor_pom_prime_residual_linear_lb_PomRewriteStrategy :=
  {T : ℕ → ℚ //
    ∀ m : ℕ, Omega.Folding.GaugeAnomalyMean.gaugeAnomalyMeanDensity m ≤ 3 * T (m + 1)}

/-- The prime-register residual lower bound says that the rewrite density is eventually bounded
below by any rational value strictly below `4 / 27`. -/
def cor_pom_prime_residual_linear_lb_PomPrimeResidualLinearLowerBound
    (S : cor_pom_prime_residual_linear_lb_PomRewriteStrategy) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, (4 / 27 : ℚ) - ε ≤ S.1 (m + 1)

local notation "PomRewriteStrategy" =>
  cor_pom_prime_residual_linear_lb_PomRewriteStrategy

local notation "PomPrimeResidualLinearLowerBound" =>
  cor_pom_prime_residual_linear_lb_PomPrimeResidualLinearLowerBound

/-- Paper label: `cor:pom-prime-residual-linear-lb`. -/
theorem paper_pom_prime_residual_linear_lb (S : PomRewriteStrategy) :
    PomPrimeResidualLinearLowerBound S := by
  intro ε hε
  have hthreeε : 0 < 3 * ε := by positivity
  rcases Omega.Folding.GaugeAnomalyMean.paper_fold_gauge_anomaly_mean_density_monotone.2.2
      (3 * ε) hthreeε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm
  have hclose := hN m hm
  have hdensity_lower : (4 / 9 : ℚ) - 3 * ε <
      Omega.Folding.GaugeAnomalyMean.gaugeAnomalyMeanDensity m := by
    have habs := abs_lt.mp hclose
    linarith
  have hpointwise := S.2 m
  have hremainder : (4 / 9 : ℚ) - 3 * ε < 3 * S.1 (m + 1) := by
    exact lt_of_lt_of_le hdensity_lower hpointwise
  have hfinal : (4 / 27 : ℚ) - ε < S.1 (m + 1) := by
    nlinarith
  exact le_of_lt hfinal

end Omega.POM
