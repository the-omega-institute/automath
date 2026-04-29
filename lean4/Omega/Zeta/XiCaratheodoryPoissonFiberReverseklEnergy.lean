import Omega.Zeta.XiPoissonLowerboundReverseKLL2

namespace Omega.Zeta

/-- Paper label: `thm:xi-caratheodory-poisson-fiber-reversekl-energy`. -/
theorem paper_xi_caratheodory_poisson_fiber_reversekl_energy
    (r reverseKL coefficientEnergy l2Energy : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hL2 : l2Energy = 2 * coefficientEnergy)
    (hKL :
      reverseKL ≤
        xi_reversekl_chi2_optimal_under_lower_bound_kappa ((1 - r) / (1 + r)) *
          l2Energy) :
    reverseKL ≤
      2 * xi_reversekl_chi2_optimal_under_lower_bound_kappa ((1 - r) / (1 + r)) *
        coefficientEnergy := by
  have _ : 0 < r := hr0
  have _ : r < 1 := hr1
  calc
    reverseKL ≤
        xi_reversekl_chi2_optimal_under_lower_bound_kappa ((1 - r) / (1 + r)) *
          l2Energy := hKL
    _ =
        2 * xi_reversekl_chi2_optimal_under_lower_bound_kappa ((1 - r) / (1 + r)) *
          coefficientEnergy := by
      rw [hL2]
      ring

end Omega.Zeta
