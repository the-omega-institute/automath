import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite signed-measure data for the two-block escort normal form. -/
structure xi_time_part9l_escort_two_block_normal_form_data where
  xi_time_part9l_escort_two_block_normal_form_card : ℕ
  xi_time_part9l_escort_two_block_normal_form_pi :
    Fin xi_time_part9l_escort_two_block_normal_form_card → ℝ
  xi_time_part9l_escort_two_block_normal_form_lambda :
    Fin xi_time_part9l_escort_two_block_normal_form_card → ℝ
  xi_time_part9l_escort_two_block_normal_form_tvBound : ℝ
  xi_time_part9l_escort_two_block_normal_form_pi_mass :
    (Finset.univ.sum xi_time_part9l_escort_two_block_normal_form_pi) = 1
  xi_time_part9l_escort_two_block_normal_form_lambda_mass :
    (Finset.univ.sum xi_time_part9l_escort_two_block_normal_form_lambda) = 1
  xi_time_part9l_escort_two_block_normal_form_tv_sufficiency :
    (Finset.univ.sum fun x =>
        |xi_time_part9l_escort_two_block_normal_form_pi x -
          xi_time_part9l_escort_two_block_normal_form_lambda x|) ≤
      xi_time_part9l_escort_two_block_normal_form_tvBound

namespace xi_time_part9l_escort_two_block_normal_form_data

/-- The residual signed measure `π - Λ`. -/
def xi_time_part9l_escort_two_block_normal_form_residual
    (D : xi_time_part9l_escort_two_block_normal_form_data) :
    Fin D.xi_time_part9l_escort_two_block_normal_form_card → ℝ :=
  fun x =>
    D.xi_time_part9l_escort_two_block_normal_form_pi x -
      D.xi_time_part9l_escort_two_block_normal_form_lambda x

/-- Total variation norm of the residual signed measure. -/
def xi_time_part9l_escort_two_block_normal_form_residual_tv
    (D : xi_time_part9l_escort_two_block_normal_form_data) : ℝ :=
  Finset.univ.sum fun x =>
    |D.xi_time_part9l_escort_two_block_normal_form_residual x|

/-- The residual has zero total mass and inherits the supplied TV sufficiency estimate. -/
def statement (D : xi_time_part9l_escort_two_block_normal_form_data) : Prop :=
  (Finset.univ.sum D.xi_time_part9l_escort_two_block_normal_form_residual = 0) ∧
    D.xi_time_part9l_escort_two_block_normal_form_residual_tv ≤
      D.xi_time_part9l_escort_two_block_normal_form_tvBound

end xi_time_part9l_escort_two_block_normal_form_data

/-- Paper label: `cor:xi-time-part9l-escort-two-block-normal-form`. -/
theorem paper_xi_time_part9l_escort_two_block_normal_form
    (D : xi_time_part9l_escort_two_block_normal_form_data) : D.statement := by
  constructor
  · simp [
      xi_time_part9l_escort_two_block_normal_form_data.xi_time_part9l_escort_two_block_normal_form_residual,
      Finset.sum_sub_distrib,
      D.xi_time_part9l_escort_two_block_normal_form_pi_mass,
      D.xi_time_part9l_escort_two_block_normal_form_lambda_mass]
  · simpa [xi_time_part9l_escort_two_block_normal_form_data.statement,
      xi_time_part9l_escort_two_block_normal_form_data.xi_time_part9l_escort_two_block_normal_form_residual_tv,
      xi_time_part9l_escort_two_block_normal_form_data.xi_time_part9l_escort_two_block_normal_form_residual]
      using D.xi_time_part9l_escort_two_block_normal_form_tv_sufficiency

end Omega.Zeta
