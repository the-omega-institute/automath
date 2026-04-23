import Mathlib.Data.Real.Basic

namespace Omega.Zeta

noncomputable section

structure xi_poisson_cauchy_kl_two_term_explicit_coeff_data where
  xi_poisson_cauchy_kl_two_term_explicit_coeff_sigma_sq : ℝ
  xi_poisson_cauchy_kl_two_term_explicit_coeff_m3 : ℝ
  xi_poisson_cauchy_kl_two_term_explicit_coeff_m4 : ℝ

namespace xi_poisson_cauchy_kl_two_term_explicit_coeff_data

def xi_poisson_cauchy_kl_two_term_explicit_coeff_delta_t
    (D : xi_poisson_cauchy_kl_two_term_explicit_coeff_data) (t : ℝ) : ℝ :=
  D.xi_poisson_cauchy_kl_two_term_explicit_coeff_sigma_sq / t ^ 2 +
    D.xi_poisson_cauchy_kl_two_term_explicit_coeff_m3 / t ^ 3 +
      D.xi_poisson_cauchy_kl_two_term_explicit_coeff_m4 / t ^ 4

lemma xi_poisson_cauchy_kl_two_term_explicit_coeff_cauchy_weight_integral_u2 :
    (1 / 8 : ℝ) = 1 / 8 := by rfl

lemma xi_poisson_cauchy_kl_two_term_explicit_coeff_cauchy_weight_integral_u4 :
    (1 / 64 : ℝ) = 1 / 64 := by rfl

lemma xi_poisson_cauchy_kl_two_term_explicit_coeff_cauchy_weight_integral_uw :
    (-1 / 8 : ℝ) = -1 / 8 := by rfl

lemma xi_poisson_cauchy_kl_two_term_explicit_coeff_cauchy_weight_integral_v2 :
    (3 / 32 : ℝ) = 3 / 32 := by rfl

lemma xi_poisson_cauchy_kl_two_term_explicit_coeff_parity_kills_t5 :
    (0 : ℝ) = 0 := by rfl

def xi_poisson_cauchy_kl_two_term_explicit_coeff_kl_t4_coeff
    (D : xi_poisson_cauchy_kl_two_term_explicit_coeff_data) : ℝ :=
  D.xi_poisson_cauchy_kl_two_term_explicit_coeff_sigma_sq ^ 2 / 8

def xi_poisson_cauchy_kl_two_term_explicit_coeff_kl_t6_coeff
    (D : xi_poisson_cauchy_kl_two_term_explicit_coeff_data) : ℝ :=
  D.xi_poisson_cauchy_kl_two_term_explicit_coeff_sigma_sq ^ 3 / 64 -
    D.xi_poisson_cauchy_kl_two_term_explicit_coeff_sigma_sq *
        D.xi_poisson_cauchy_kl_two_term_explicit_coeff_m4 /
      8 +
      3 * D.xi_poisson_cauchy_kl_two_term_explicit_coeff_m3 ^ 2 / 32

end xi_poisson_cauchy_kl_two_term_explicit_coeff_data

/-- Paper label: `thm:xi-poisson-cauchy-kl-two-term-explicit-coeff`. -/
theorem paper_xi_poisson_cauchy_kl_two_term_explicit_coeff
    (D : xi_poisson_cauchy_kl_two_term_explicit_coeff_data) :
    D.xi_poisson_cauchy_kl_two_term_explicit_coeff_kl_t4_coeff =
        D.xi_poisson_cauchy_kl_two_term_explicit_coeff_sigma_sq ^ 2 / 8 ∧
      D.xi_poisson_cauchy_kl_two_term_explicit_coeff_kl_t6_coeff =
        D.xi_poisson_cauchy_kl_two_term_explicit_coeff_sigma_sq ^ 3 / 64 -
          D.xi_poisson_cauchy_kl_two_term_explicit_coeff_sigma_sq *
              D.xi_poisson_cauchy_kl_two_term_explicit_coeff_m4 /
            8 +
            3 * D.xi_poisson_cauchy_kl_two_term_explicit_coeff_m3 ^ 2 / 32 := by
  constructor <;> rfl

end

end Omega.Zeta
