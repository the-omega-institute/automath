import Omega.Zeta.XiPoissonCauchyKlTwoTermExplicitCoeff

namespace Omega.Zeta

/-- Paper label: `thm:xi-poisson-kl-sixth-order-mu3-mu4`. -/
theorem paper_xi_poisson_kl_sixth_order_mu3_mu4
    (D : xi_poisson_cauchy_kl_two_term_explicit_coeff_data) :
    D.xi_poisson_cauchy_kl_two_term_explicit_coeff_kl_t6_coeff =
      D.xi_poisson_cauchy_kl_two_term_explicit_coeff_sigma_sq ^ 3 / 64 -
        D.xi_poisson_cauchy_kl_two_term_explicit_coeff_sigma_sq *
            D.xi_poisson_cauchy_kl_two_term_explicit_coeff_m4 /
          8 +
          3 * D.xi_poisson_cauchy_kl_two_term_explicit_coeff_m3 ^ 2 / 32 := by
  rfl

end Omega.Zeta
