import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/--
Concrete coefficient package for the sixth-order Poisson--Cauchy KL expansion.

The integral constants are kept as fields so the paper-facing theorem can
record the Taylor/Gaussian-integral interface and then close by arithmetic.
-/
structure xi_poisson_kl_sixth_order_refined_binomials_data where
  xi_poisson_kl_sixth_order_refined_binomials_sigmaSq : ℝ
  xi_poisson_kl_sixth_order_refined_binomials_m3 : ℝ
  xi_poisson_kl_sixth_order_refined_binomials_m4 : ℝ
  xi_poisson_kl_sixth_order_refined_binomials_integral_U2_sq : ℝ
  xi_poisson_kl_sixth_order_refined_binomials_integral_V3_sq : ℝ
  xi_poisson_kl_sixth_order_refined_binomials_integral_U2W4 : ℝ
  xi_poisson_kl_sixth_order_refined_binomials_integral_U2_cube : ℝ
  xi_poisson_kl_sixth_order_refined_binomials_integral_U2_sq_eq :
    xi_poisson_kl_sixth_order_refined_binomials_integral_U2_sq = 1 / 4
  xi_poisson_kl_sixth_order_refined_binomials_integral_V3_sq_eq :
    xi_poisson_kl_sixth_order_refined_binomials_integral_V3_sq = 3 / 16
  xi_poisson_kl_sixth_order_refined_binomials_integral_U2W4_eq :
    xi_poisson_kl_sixth_order_refined_binomials_integral_U2W4 = -1 / 8
  xi_poisson_kl_sixth_order_refined_binomials_integral_U2_cube_eq :
    xi_poisson_kl_sixth_order_refined_binomials_integral_U2_cube = -3 / 32

namespace xi_poisson_kl_sixth_order_refined_binomials_data

/-- Raw `t^-4` coefficient before inserting the Gaussian integral. -/
def xi_poisson_kl_sixth_order_refined_binomials_raw_t4
    (D : xi_poisson_kl_sixth_order_refined_binomials_data) : ℝ :=
  (1 / 2 : ℝ) * D.xi_poisson_kl_sixth_order_refined_binomials_sigmaSq ^ 2 *
    D.xi_poisson_kl_sixth_order_refined_binomials_integral_U2_sq

/-- Closed `t^-4` coefficient. -/
def xi_poisson_kl_sixth_order_refined_binomials_closed_t4
    (D : xi_poisson_kl_sixth_order_refined_binomials_data) : ℝ :=
  D.xi_poisson_kl_sixth_order_refined_binomials_sigmaSq ^ 2 / 8

/-- Raw `t^-6` coefficient before inserting the Gaussian integrals. -/
def xi_poisson_kl_sixth_order_refined_binomials_raw_t6
    (D : xi_poisson_kl_sixth_order_refined_binomials_data) : ℝ :=
  (1 / 2 : ℝ) *
      (D.xi_poisson_kl_sixth_order_refined_binomials_m3 ^ 2 *
          D.xi_poisson_kl_sixth_order_refined_binomials_integral_V3_sq +
        2 * D.xi_poisson_kl_sixth_order_refined_binomials_sigmaSq *
          D.xi_poisson_kl_sixth_order_refined_binomials_m4 *
            D.xi_poisson_kl_sixth_order_refined_binomials_integral_U2W4) -
    (1 / 6 : ℝ) * D.xi_poisson_kl_sixth_order_refined_binomials_sigmaSq ^ 3 *
      D.xi_poisson_kl_sixth_order_refined_binomials_integral_U2_cube

/-- Closed `t^-6` KL coefficient. -/
def xi_poisson_kl_sixth_order_refined_binomials_closed_t6
    (D : xi_poisson_kl_sixth_order_refined_binomials_data) : ℝ :=
  D.xi_poisson_kl_sixth_order_refined_binomials_sigmaSq ^ 3 / 64 +
    3 * D.xi_poisson_kl_sixth_order_refined_binomials_m3 ^ 2 / 32 -
      D.xi_poisson_kl_sixth_order_refined_binomials_sigmaSq *
        D.xi_poisson_kl_sixth_order_refined_binomials_m4 / 8

/-- The coefficient form of the paper's KL asymptotic through order `t^-6`. -/
def xi_poisson_kl_sixth_order_refined_binomials_kl_asymptotic
    (D : xi_poisson_kl_sixth_order_refined_binomials_data) : Prop :=
  D.xi_poisson_kl_sixth_order_refined_binomials_raw_t4 =
      D.xi_poisson_kl_sixth_order_refined_binomials_closed_t4 ∧
    D.xi_poisson_kl_sixth_order_refined_binomials_raw_t6 =
      D.xi_poisson_kl_sixth_order_refined_binomials_closed_t6

end xi_poisson_kl_sixth_order_refined_binomials_data

open xi_poisson_kl_sixth_order_refined_binomials_data

/-- Paper label: `thm:xi-poisson-kl-sixth-order-refined-binomials`. -/
theorem paper_xi_poisson_kl_sixth_order_refined_binomials
    (D : xi_poisson_kl_sixth_order_refined_binomials_data) :
    D.xi_poisson_kl_sixth_order_refined_binomials_kl_asymptotic := by
  constructor
  · rw [xi_poisson_kl_sixth_order_refined_binomials_raw_t4,
      xi_poisson_kl_sixth_order_refined_binomials_closed_t4,
      D.xi_poisson_kl_sixth_order_refined_binomials_integral_U2_sq_eq]
    ring
  · rw [xi_poisson_kl_sixth_order_refined_binomials_raw_t6,
      xi_poisson_kl_sixth_order_refined_binomials_closed_t6,
      D.xi_poisson_kl_sixth_order_refined_binomials_integral_V3_sq_eq,
      D.xi_poisson_kl_sixth_order_refined_binomials_integral_U2W4_eq,
      D.xi_poisson_kl_sixth_order_refined_binomials_integral_U2_cube_eq]
    ring

end

end Omega.Zeta
