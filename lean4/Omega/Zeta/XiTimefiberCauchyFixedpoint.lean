import Mathlib.Tactic
import Omega.Zeta.TimefiberPoissonProjectionPrinciple

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-timefiber-cauchy-fixedpoint`. The time-fiber Poisson projection
principle identifies the pushed law with the Cauchy average, and evaluation at `i` fixes the
given Cauchy law. -/
theorem paper_xi_timefiber_cauchy_fixedpoint
    (rho lawU lawU' : ℝ) (hrho : 0 < rho ∧ rho < 1)
    (hpush : lawU' = xi_timefiber_poisson_projection_principle_ring_average rho lawU)
    (hlaw : lawU = xi_timefiber_poisson_projection_principle_at_i lawU) :
    lawU' = lawU := by
  rcases paper_xi_timefiber_poisson_projection_principle rho lawU hrho with ⟨hring, hcauchy⟩
  calc
    lawU' = xi_timefiber_poisson_projection_principle_ring_average rho lawU := hpush
    _ = xi_timefiber_poisson_projection_principle_cauchy_average lawU := hring
    _ = xi_timefiber_poisson_projection_principle_at_i lawU := hcauchy
    _ = lawU := hlaw.symm

end

end Omega.Zeta
