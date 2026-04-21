import Omega.CircleDimension.PoissonKLMomentMatchingLeadingTerm
import Omega.CircleDimension.PoissonKLQuadraticFormSpectral

namespace Omega.CircleDimension

/-- The rescaled moment profile used in the quadratic-form package. -/
noncomputable def poissonRescaledMomentDifference (t : ℝ) (μ ν : ℕ → ℝ) (n : ℕ) : ℝ :=
  poissonMomentDifference μ ν n / t ^ (n - 1)

/-- Chapter-local formulation of the all-moment Poisson KL quadratic-form package. It records the
moment-cancellation asymptotic coefficient together with the derivative-Gram and kernel closed
forms used to rewrite the quadratic term as a positive spectral energy. -/
def PoissonKLAllMomentQuadraticForm
    (m : ℕ) (barycenter klCoeff t : ℝ) (μ ν : ℕ → ℝ) (D : PoissonKLQuadraticFormSpectralData) :
    Prop :=
  poissonCommonBarycenter barycenter μ ν ∧
    poissonMomentsMatchUpTo m μ ν ∧
    klCoeff = poissonKLMomentMatchingLeadingCoefficient m μ ν ∧
    (∀ x : ℝ, poissonKLQuadraticKernel x = cauchyDerivativeGramExponentialKernelValue x 0) ∧
    cdimCauchyDerivativeGram 1 1 1 = cdimCauchyDerivativeGramClosedForm 1 1 1 ∧
    poissonRescaledMomentDifference t μ ν m = poissonMomentDifference μ ν m / t ^ (m - 1) ∧
    PoissonKLQuadraticFormSpectral D

/-- The moment-matching leading coefficient, the derivative-Gram closed form, and the exponential
kernel identity combine into the quadratic-form/spectral package used in the paper.
    prop:cdim-poisson-kl-all-moment-quadratic-form -/
theorem paper_cdim_poisson_kl_all_moment_quadratic_form
    (m : ℕ) (barycenter klCoeff t : ℝ) (μ ν : ℕ → ℝ) (D : PoissonKLQuadraticFormSpectralData)
    (hBarycenter : poissonCommonBarycenter barycenter μ ν)
    (hMatch : ∀ k, k < m → μ k = ν k)
    (hKL :
      klCoeff = poissonHigherOrderFisherEnergy m μ ν / ((2 : ℝ) * Nat.factorial m)) :
    PoissonKLAllMomentQuadraticForm m barycenter klCoeff t μ ν D := by
  have hMoment :=
    paper_cdim_poisson_kl_moment_matching_leading_term m barycenter klCoeff μ ν
      hBarycenter hMatch hKL
  have hSpectral := paper_cdim_poisson_kl_quadratic_form_spectral D
  refine ⟨hMoment.1, hMoment.2.1, hMoment.2.2, ?_, ?_, rfl, hSpectral⟩
  · intro x
    rfl
  · simpa using
      paper_cdim_cauchy_kernel_derivative_gram_closed_form 1 1 (by omega) (by omega) 1
        (by positivity)

end Omega.CircleDimension
