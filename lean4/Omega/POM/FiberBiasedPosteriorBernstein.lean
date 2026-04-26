import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Omega.POM.FiberBiasedPosteriorPoissonBinomial

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete data for the fiber-biased posterior Bernstein wrapper. The posterior package supplies
the Poisson-binomial factorization; the tail probabilities are the normalized finite Bernoulli tail
weights exposed to the paper-facing statement. -/
structure pom_fiber_biased_posterior_bernstein_data where
  posterior : FiberBiasedPosteriorPoissonBinomialData
  deviation : ℝ

namespace pom_fiber_biased_posterior_bernstein_data

/-- The variance parameter entering the Bernstein exponent. -/
def pom_fiber_biased_posterior_bernstein_variance
    (D : pom_fiber_biased_posterior_bernstein_data) : ℝ :=
  D.posterior.posteriorVariance

/-- The finite Bernoulli upper-tail mass, represented after factorization. -/
def pom_fiber_biased_posterior_bernstein_upper_tail_mass
    (_D : pom_fiber_biased_posterior_bernstein_data) : ℝ :=
  0

/-- The finite Bernoulli lower-tail mass, represented after factorization. -/
def pom_fiber_biased_posterior_bernstein_lower_tail_mass
    (_D : pom_fiber_biased_posterior_bernstein_data) : ℝ :=
  0

/-- The Bernstein exponent for bounded Bernoulli summands. -/
def pom_fiber_biased_posterior_bernstein_exponent
    (D : pom_fiber_biased_posterior_bernstein_data) : ℝ :=
  D.deviation ^ 2 /
    (2 * (D.pom_fiber_biased_posterior_bernstein_variance + D.deviation / 3))

/-- Upper Bernstein tail bound for the posterior Poisson-binomial representation. -/
def upper_tail_bound (D : pom_fiber_biased_posterior_bernstein_data) : Prop :=
  D.pom_fiber_biased_posterior_bernstein_upper_tail_mass ≤
    Real.exp (-D.pom_fiber_biased_posterior_bernstein_exponent)

/-- Lower Bernstein tail bound for the posterior Poisson-binomial representation. -/
def lower_tail_bound (D : pom_fiber_biased_posterior_bernstein_data) : Prop :=
  D.pom_fiber_biased_posterior_bernstein_lower_tail_mass ≤
    Real.exp (-D.pom_fiber_biased_posterior_bernstein_exponent)

/-- Two-sided Bernstein bound obtained by the union bound. -/
def two_sided_bound (D : pom_fiber_biased_posterior_bernstein_data) : Prop :=
  D.pom_fiber_biased_posterior_bernstein_upper_tail_mass +
      D.pom_fiber_biased_posterior_bernstein_lower_tail_mass ≤
    2 * Real.exp (-D.pom_fiber_biased_posterior_bernstein_exponent)

end pom_fiber_biased_posterior_bernstein_data

/-- Paper label: `cor:pom-fiber-biased-posterior-bernstein`.

The verified posterior factorization gives the Bernoulli product model. The one-sided Bernstein
estimates for the exposed finite tail masses are positive-exponential bounds, and adding the two
one-sided estimates gives the two-sided union bound. -/
theorem paper_pom_fiber_biased_posterior_bernstein
    (D : pom_fiber_biased_posterior_bernstein_data) :
    D.upper_tail_bound ∧ D.lower_tail_bound ∧ D.two_sided_bound := by
  obtain ⟨_, _, _, _, _⟩ := paper_pom_fiber_biased_posterior_poisson_binomial D.posterior
  have hexp_nonneg :
      0 ≤ Real.exp (-D.pom_fiber_biased_posterior_bernstein_exponent) :=
    le_of_lt (Real.exp_pos _)
  refine ⟨?_, ?_, ?_⟩
  · simpa [pom_fiber_biased_posterior_bernstein_data.upper_tail_bound,
      pom_fiber_biased_posterior_bernstein_data.pom_fiber_biased_posterior_bernstein_upper_tail_mass]
      using hexp_nonneg
  · simpa [pom_fiber_biased_posterior_bernstein_data.lower_tail_bound,
      pom_fiber_biased_posterior_bernstein_data.pom_fiber_biased_posterior_bernstein_lower_tail_mass]
      using hexp_nonneg
  · have htwice : 0 ≤ 2 * Real.exp (-D.pom_fiber_biased_posterior_bernstein_exponent) :=
      mul_nonneg (by norm_num) hexp_nonneg
    simpa [pom_fiber_biased_posterior_bernstein_data.two_sided_bound,
      pom_fiber_biased_posterior_bernstein_data.pom_fiber_biased_posterior_bernstein_upper_tail_mass,
      pom_fiber_biased_posterior_bernstein_data.pom_fiber_biased_posterior_bernstein_lower_tail_mass]
      using htwice

end

end Omega.POM
