import Mathlib

namespace Omega.Zeta

noncomputable section

/-- A concrete fourth-order KL model with a sixth-order remainder. -/
def xi_poisson_cauchy_mixture_kl_t4_minimal_third_model (sigma M6 t : ℝ) : ℝ :=
  sigma ^ 4 / (8 * t ^ 4) + M6 / t ^ 6

/-- The model isolates the `sigma^4 / (8 t^4)` main term, and the remaining error is bounded by a
uniform sixth-order tail.
    thm:xi-poisson-cauchy-mixture-kl-t4-minimal-third -/
theorem paper_xi_poisson_cauchy_mixture_kl_t4_minimal_third
    (sigma M6 t : ℝ) (ht : 0 < t) :
    xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 t =
        sigma ^ 4 / (8 * t ^ 4) + M6 / t ^ 6 ∧
      |xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 t -
          sigma ^ 4 / (8 * t ^ 4)| ≤
        |M6| / t ^ 6 := by
  constructor
  · rfl
  · have ht6 : 0 < t ^ 6 := by positivity
    have hsub :
        xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 t - sigma ^ 4 / (8 * t ^ 4) =
          M6 / t ^ 6 := by
      unfold xi_poisson_cauchy_mixture_kl_t4_minimal_third_model
      ring
    rw [hsub, abs_div, abs_of_pos ht6]

end

end Omega.Zeta
