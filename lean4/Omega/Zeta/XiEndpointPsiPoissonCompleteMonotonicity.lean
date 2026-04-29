import Omega.Zeta.XiEndpointPsiPoissonShiftLoewnerMonotone

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `cor:xi-endpoint-psi-poisson-complete-monotonicity`. Each signed derivative
proxy is a finite sum of nonnegative Poisson-shift terms. -/
theorem paper_xi_endpoint_psi_poisson_complete_monotonicity
    (D : XiEndpointPsiPoissonShiftLoewnerMonotoneData) :
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ m : Fin D.J → ℝ,
      0 ≤ ∑ j,
        (2 : ℝ) ^ n * (m j * D.amplitude j) ^ 2 * (D.decay j) ^ n *
          Real.exp (t * (-2 * D.decay j)) := by
  intro n t _ m
  refine Finset.sum_nonneg ?_
  intro j _
  have htwo : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) n
  have hsq : 0 ≤ (m j * D.amplitude j) ^ 2 := sq_nonneg _
  have hdecay : 0 ≤ (D.decay j) ^ n := pow_nonneg (D.decay_nonneg j) n
  have hexp : 0 ≤ Real.exp (t * (-2 * D.decay j)) := le_of_lt (Real.exp_pos _)
  exact mul_nonneg (mul_nonneg (mul_nonneg htwo hsq) hdecay) hexp

end Omega.Zeta
