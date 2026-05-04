import Omega.Zeta.XiCauchyPoissonTwoChannelOrthogonalLeading

namespace Omega.Zeta

noncomputable section

/-- Concrete two-parameter Poisson--Cauchy KL package. -/
structure xi_poisson_two_parameter_kl_sharp_quadratic_data where
  var_gamma : ℝ
  var_delta : ℝ
  cov_gamma_delta : ℝ

namespace xi_poisson_two_parameter_kl_sharp_quadratic_data

/-- The two orthogonal coordinates: even variance gap and odd covariance channel. -/
def xi_poisson_two_parameter_kl_sharp_quadratic_coordinates
    (D : xi_poisson_two_parameter_kl_sharp_quadratic_data) : ℝ × ℝ :=
  (D.var_gamma - D.var_delta, D.cov_gamma_delta)

/-- The sharp quadratic KL limit as the leading two-channel Poisson--Cauchy coefficient. -/
def kl_sharp_limit (D : xi_poisson_two_parameter_kl_sharp_quadratic_data) : ℝ :=
  xi_cauchy_poisson_two_channel_orthogonal_leading_constant
    D.xi_poisson_two_parameter_kl_sharp_quadratic_coordinates.1
    D.xi_poisson_two_parameter_kl_sharp_quadratic_coordinates.2

end xi_poisson_two_parameter_kl_sharp_quadratic_data

open xi_poisson_two_parameter_kl_sharp_quadratic_data

/-- Paper label: `thm:xi-poisson-two-parameter-kl-sharp-quadratic`. The even variance-gap
coordinate and odd covariance coordinate are orthogonal, so the sharp KL coefficient is the sum of
their two quadratic contributions. -/
theorem paper_xi_poisson_two_parameter_kl_sharp_quadratic
    (D : xi_poisson_two_parameter_kl_sharp_quadratic_data) :
    D.kl_sharp_limit = (D.var_gamma - D.var_delta) ^ 2 / 8 + D.cov_gamma_delta ^ 2 / 2 := by
  simp [kl_sharp_limit, xi_poisson_two_parameter_kl_sharp_quadratic_coordinates,
    xi_cauchy_poisson_two_channel_orthogonal_leading_constant]

end

end Omega.Zeta
