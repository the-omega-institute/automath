import Mathlib.Tactic
import Omega.Zeta.PoissonCauchyMixtureKLT4MinimalThird

namespace Omega.Zeta

noncomputable section

/-- The centered second-moment gap controlling the fourth-order Poisson--Cauchy KL coefficient. -/
def xi_poisson_cauchy_kl_fourth_order_universality_second_moment_gap (sigma : ℝ) : ℝ :=
  sigma ^ 2

/-- The universal fourth-order main term attached to the second-moment gap. -/
def xi_poisson_cauchy_kl_fourth_order_universality_main_term (sigma t : ℝ) : ℝ :=
  xi_poisson_cauchy_kl_fourth_order_universality_second_moment_gap sigma ^ 2 / (8 * t ^ 4)

/-- Paper label: `thm:xi-poisson-cauchy-kl-fourth-order-universality`.
The fourth-order Poisson--Cauchy KL model depends on the profile only through the squared
second-moment gap, and the leading coefficient is the universal `1/8`. -/
theorem paper_xi_poisson_cauchy_kl_fourth_order_universality
    (sigma M6 t : ℝ) (ht : 0 < t) :
    xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 t =
        xi_poisson_cauchy_kl_fourth_order_universality_main_term sigma t + M6 / t ^ 6 ∧
      |xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 t -
          xi_poisson_cauchy_kl_fourth_order_universality_main_term sigma t| ≤
        |M6| / t ^ 6 ∧
      xi_poisson_cauchy_kl_fourth_order_universality_main_term sigma t = sigma ^ 4 / (8 * t ^ 4) := by
  rcases paper_xi_poisson_cauchy_mixture_kl_t4_minimal_third sigma M6 t ht with ⟨hModel, hErr⟩
  have hMain :
      xi_poisson_cauchy_kl_fourth_order_universality_main_term sigma t = sigma ^ 4 / (8 * t ^ 4) := by
    unfold xi_poisson_cauchy_kl_fourth_order_universality_main_term
      xi_poisson_cauchy_kl_fourth_order_universality_second_moment_gap
    have hsigma : (sigma ^ 2) ^ 2 = sigma ^ 4 := by
      calc
        (sigma ^ 2) ^ 2 = sigma ^ (2 * 2) := by rw [← pow_mul]
        _ = sigma ^ 4 := by norm_num
    rw [hsigma]
  refine ⟨?_, ?_, ?_⟩
  · calc
      xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 t =
          sigma ^ 4 / (8 * t ^ 4) + M6 / t ^ 6 := hModel
      _ = xi_poisson_cauchy_kl_fourth_order_universality_main_term sigma t + M6 / t ^ 6 := by
        rw [hMain]
  · calc
      |xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 t -
          xi_poisson_cauchy_kl_fourth_order_universality_main_term sigma t| =
          |xi_poisson_cauchy_mixture_kl_t4_minimal_third_model sigma M6 t -
            sigma ^ 4 / (8 * t ^ 4)| := by rw [hMain]
      _ ≤ |M6| / t ^ 6 := hErr
  · exact hMain

end

end Omega.Zeta
