import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

def xi_poisson_fdiv_sixth_order_mu3_mu4_integral_U2_sq : ℝ := 1 / 4

def xi_poisson_fdiv_sixth_order_mu3_mu4_integral_V3_sq : ℝ := 3 / 16

def xi_poisson_fdiv_sixth_order_mu3_mu4_integral_U2W4 : ℝ := -1 / 8

def xi_poisson_fdiv_sixth_order_mu3_mu4_integral_U2_cube : ℝ := -3 / 32

def xi_poisson_fdiv_sixth_order_mu3_mu4_raw_t4 (f2 sigmaSq : ℝ) : ℝ :=
  (f2 / 2) * sigmaSq ^ 2 * xi_poisson_fdiv_sixth_order_mu3_mu4_integral_U2_sq

def xi_poisson_fdiv_sixth_order_mu3_mu4_closed_t4 (f2 sigmaSq : ℝ) : ℝ :=
  f2 * sigmaSq ^ 2 / 8

def xi_poisson_fdiv_sixth_order_mu3_mu4_raw_t6
    (f2 f3 sigmaSq mu3 mu4 : ℝ) : ℝ :=
  (f2 / 2) *
      (mu3 ^ 2 * xi_poisson_fdiv_sixth_order_mu3_mu4_integral_V3_sq +
        2 * sigmaSq * mu4 * xi_poisson_fdiv_sixth_order_mu3_mu4_integral_U2W4) +
    (f3 / 6) * sigmaSq ^ 3 *
      xi_poisson_fdiv_sixth_order_mu3_mu4_integral_U2_cube

def xi_poisson_fdiv_sixth_order_mu3_mu4_closed_t6
    (f2 f3 sigmaSq mu3 mu4 : ℝ) : ℝ :=
  f2 * (3 * mu3 ^ 2 / 32 - sigmaSq * mu4 / 8) - f3 * sigmaSq ^ 3 / 64

def xi_poisson_fdiv_sixth_order_mu3_mu4_asymptotic
    (f2 f3 sigmaSq mu3 mu4 : ℝ) : Prop :=
  xi_poisson_fdiv_sixth_order_mu3_mu4_raw_t4 f2 sigmaSq =
      xi_poisson_fdiv_sixth_order_mu3_mu4_closed_t4 f2 sigmaSq ∧
    xi_poisson_fdiv_sixth_order_mu3_mu4_raw_t6 f2 f3 sigmaSq mu3 mu4 =
      xi_poisson_fdiv_sixth_order_mu3_mu4_closed_t6 f2 f3 sigmaSq mu3 mu4

/-- Paper label: `prop:xi-poisson-fdiv-sixth-order-mu3-mu4`. -/
theorem paper_xi_poisson_fdiv_sixth_order_mu3_mu4
    (f2 f3 sigmaSq mu3 mu4 : ℝ) :
    xi_poisson_fdiv_sixth_order_mu3_mu4_asymptotic f2 f3 sigmaSq mu3 mu4 := by
  constructor <;>
    simp [xi_poisson_fdiv_sixth_order_mu3_mu4_raw_t4,
      xi_poisson_fdiv_sixth_order_mu3_mu4_closed_t4,
      xi_poisson_fdiv_sixth_order_mu3_mu4_raw_t6,
      xi_poisson_fdiv_sixth_order_mu3_mu4_closed_t6,
      xi_poisson_fdiv_sixth_order_mu3_mu4_integral_U2_sq,
      xi_poisson_fdiv_sixth_order_mu3_mu4_integral_V3_sq,
      xi_poisson_fdiv_sixth_order_mu3_mu4_integral_U2W4,
      xi_poisson_fdiv_sixth_order_mu3_mu4_integral_U2_cube] <;>
    ring

end

end Omega.Zeta
