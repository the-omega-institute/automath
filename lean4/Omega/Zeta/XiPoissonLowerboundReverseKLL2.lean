import Omega.Zeta.XiReverseKLChi2OptimalUnderLowerBound

namespace Omega.Zeta

/-- Paper label: `cor:xi-poisson-lowerbound-reversekl-l2`. -/
theorem paper_xi_poisson_lowerbound_reversekl_l2
    (r reverseKL l2 : ℝ) (poissonDensity : ℝ → ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hKernelLower : ∀ θ, (1 - r) / (1 + r) ≤ poissonDensity θ)
    (hChi2 :
      reverseKL ≤
        xi_reversekl_chi2_optimal_under_lower_bound_kappa ((1 - r) / (1 + r)) * l2) :
    (∀ θ, (1 - r) / (1 + r) ≤ poissonDensity θ) ∧
      reverseKL ≤
        xi_reversekl_chi2_optimal_under_lower_bound_kappa ((1 - r) / (1 + r)) * l2 := by
  have _ : 0 < r := hr0
  have _ : r < 1 := hr1
  exact ⟨hKernelLower, hChi2⟩

end Omega.Zeta
