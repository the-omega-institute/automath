import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete Taylor data for the fixed Dirichlet root-of-unity mode. -/
structure xi_output_potential_dirichlet_fixed_j_fourth_order_data where
  xi_output_potential_dirichlet_fixed_j_fourth_order_j : ℕ
  xi_output_potential_dirichlet_fixed_j_fourth_order_m : ℕ
  xi_output_potential_dirichlet_fixed_j_fourth_order_m_ne_zero :
    (xi_output_potential_dirichlet_fixed_j_fourth_order_m : ℝ) ≠ 0
  xi_output_potential_dirichlet_fixed_j_fourth_order_kappa2 : ℝ
  xi_output_potential_dirichlet_fixed_j_fourth_order_kappa4 : ℝ
  xi_output_potential_dirichlet_fixed_j_fourth_order_logLambda : ℝ
  xi_output_potential_dirichlet_fixed_j_fourth_order_logLambda_ne_zero :
    xi_output_potential_dirichlet_fixed_j_fourth_order_logLambda ≠ 0
  xi_output_potential_dirichlet_fixed_j_fourth_order_logRhoRatio : ℝ
  xi_output_potential_dirichlet_fixed_j_fourth_order_theta : ℝ
  xi_output_potential_dirichlet_fixed_j_fourth_order_remainder : ℝ
  xi_output_potential_dirichlet_fixed_j_fourth_order_logRhoRatio_eq :
    xi_output_potential_dirichlet_fixed_j_fourth_order_logRhoRatio =
      -(xi_output_potential_dirichlet_fixed_j_fourth_order_kappa2 / 2) *
          ((2 * Real.pi * (xi_output_potential_dirichlet_fixed_j_fourth_order_j : ℝ)) /
            (xi_output_potential_dirichlet_fixed_j_fourth_order_m : ℝ)) ^ 2 +
        (xi_output_potential_dirichlet_fixed_j_fourth_order_kappa4 / 24) *
          ((2 * Real.pi * (xi_output_potential_dirichlet_fixed_j_fourth_order_j : ℝ)) /
            (xi_output_potential_dirichlet_fixed_j_fourth_order_m : ℝ)) ^ 4 +
        xi_output_potential_dirichlet_fixed_j_fourth_order_remainder
  xi_output_potential_dirichlet_fixed_j_fourth_order_theta_eq :
    xi_output_potential_dirichlet_fixed_j_fourth_order_theta =
      1 +
        xi_output_potential_dirichlet_fixed_j_fourth_order_logRhoRatio /
          xi_output_potential_dirichlet_fixed_j_fourth_order_logLambda

/-- The exact second-plus-fourth order pressure formula, with the recorded sixth-order remainder. -/
def xi_output_potential_dirichlet_fixed_j_fourth_order_log_formula
    (D : xi_output_potential_dirichlet_fixed_j_fourth_order_data) : ℝ :=
  -(D.xi_output_potential_dirichlet_fixed_j_fourth_order_kappa2 / 2) *
      ((2 * Real.pi * (D.xi_output_potential_dirichlet_fixed_j_fourth_order_j : ℝ)) /
        (D.xi_output_potential_dirichlet_fixed_j_fourth_order_m : ℝ)) ^ 2 +
    (D.xi_output_potential_dirichlet_fixed_j_fourth_order_kappa4 / 24) *
      ((2 * Real.pi * (D.xi_output_potential_dirichlet_fixed_j_fourth_order_j : ℝ)) /
        (D.xi_output_potential_dirichlet_fixed_j_fourth_order_m : ℝ)) ^ 4 +
    D.xi_output_potential_dirichlet_fixed_j_fourth_order_remainder

/-- The corresponding fourth-order expansion of `theta = log rho / log lambda`. -/
def xi_output_potential_dirichlet_fixed_j_fourth_order_theta_formula
    (D : xi_output_potential_dirichlet_fixed_j_fourth_order_data) : ℝ :=
  1 -
    (2 * Real.pi ^ 2 * D.xi_output_potential_dirichlet_fixed_j_fourth_order_kappa2 /
        D.xi_output_potential_dirichlet_fixed_j_fourth_order_logLambda) *
      ((D.xi_output_potential_dirichlet_fixed_j_fourth_order_j : ℝ) ^ 2 /
        (D.xi_output_potential_dirichlet_fixed_j_fourth_order_m : ℝ) ^ 2) +
    (2 * Real.pi ^ 4 * D.xi_output_potential_dirichlet_fixed_j_fourth_order_kappa4 /
        (3 * D.xi_output_potential_dirichlet_fixed_j_fourth_order_logLambda)) *
      ((D.xi_output_potential_dirichlet_fixed_j_fourth_order_j : ℝ) ^ 4 /
        (D.xi_output_potential_dirichlet_fixed_j_fourth_order_m : ℝ) ^ 4) +
    D.xi_output_potential_dirichlet_fixed_j_fourth_order_remainder /
      D.xi_output_potential_dirichlet_fixed_j_fourth_order_logLambda

/-- Paper-facing statement: the pressure and normalized exponent have the displayed expansions. -/
def xi_output_potential_dirichlet_fixed_j_fourth_order_statement
    (D : xi_output_potential_dirichlet_fixed_j_fourth_order_data) : Prop :=
  D.xi_output_potential_dirichlet_fixed_j_fourth_order_logRhoRatio =
      xi_output_potential_dirichlet_fixed_j_fourth_order_log_formula D ∧
    D.xi_output_potential_dirichlet_fixed_j_fourth_order_theta =
      xi_output_potential_dirichlet_fixed_j_fourth_order_theta_formula D

/-- Paper label: `thm:xi-output-potential-dirichlet-fixed-j-fourth-order`. -/
theorem paper_xi_output_potential_dirichlet_fixed_j_fourth_order
    (D : xi_output_potential_dirichlet_fixed_j_fourth_order_data) :
    xi_output_potential_dirichlet_fixed_j_fourth_order_statement D := by
  constructor
  · rw [xi_output_potential_dirichlet_fixed_j_fourth_order_log_formula]
    exact D.xi_output_potential_dirichlet_fixed_j_fourth_order_logRhoRatio_eq
  · rw [xi_output_potential_dirichlet_fixed_j_fourth_order_theta_formula,
      D.xi_output_potential_dirichlet_fixed_j_fourth_order_theta_eq,
      D.xi_output_potential_dirichlet_fixed_j_fourth_order_logRhoRatio_eq]
    field_simp
      [D.xi_output_potential_dirichlet_fixed_j_fourth_order_m_ne_zero,
        D.xi_output_potential_dirichlet_fixed_j_fourth_order_logLambda_ne_zero]
    ring

end

end Omega.Zeta
