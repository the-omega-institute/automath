import Omega.Zeta.XiP7S5GlobalArtinConductorsRho456
import Omega.Zeta.XiP7S5DyadicC3InertiaQuadraticFunctorsConductors

namespace Omega.Zeta

/-- Paper label: `cor:xi-p7-s5-global-conductors-schur-quadratic-tensor`. -/
theorem paper_xi_p7_s5_global_conductors_schur_quadratic_tensor (q : ℕ) :
    (xi_p7_s5_global_artin_conductors_rho456_global_conductor q 6 3,
      xi_p7_s5_global_artin_conductors_rho456_global_conductor q 4 3,
      xi_p7_s5_global_artin_conductors_rho456_global_conductor q 10 6,
      xi_p7_s5_global_artin_conductors_rho456_global_conductor q 6 6,
      xi_p7_s5_global_artin_conductors_rho456_global_conductor q 14 9,
      xi_p7_s5_global_artin_conductors_rho456_global_conductor q 10 9,
      xi_p7_s5_global_artin_conductors_rho456_global_conductor q 14 9,
      xi_p7_s5_global_artin_conductors_rho456_global_conductor q 16 12,
      xi_p7_s5_global_artin_conductors_rho456_global_conductor q 20 15) =
    (2 ^ 6 * q ^ 3, 2 ^ 4 * q ^ 3, 2 ^ 10 * q ^ 6, 2 ^ 6 * q ^ 6,
      2 ^ 14 * q ^ 9, 2 ^ 10 * q ^ 9, 2 ^ 14 * q ^ 9, 2 ^ 16 * q ^ 12,
      2 ^ 20 * q ^ 15) := by
  rfl

end Omega.Zeta
