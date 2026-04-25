import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.DerivedConsequences

/-- Concrete radius/threshold data for the RH analytic buffer package. -/
structure derived_collision_rh_analytic_buffer_layer_data where
  theta_r : ℝ
  r_theta : ℝ
  derived_collision_rh_analytic_buffer_layer_theta_r_pos : 0 < theta_r
  derived_collision_rh_analytic_buffer_layer_theta_r_lt_r_theta : theta_r < r_theta

/-- Paper label: `cor:derived-collision-rh-analytic-buffer-layer`. A positive RH threshold below
the analytic radius gives a positive buffer width, and therefore the radius/threshold ratio is
strictly larger than `1`. -/
theorem paper_derived_collision_rh_analytic_buffer_layer
    (D : derived_collision_rh_analytic_buffer_layer_data) :
    0 < D.theta_r ∧ D.theta_r < D.r_theta ∧ 0 < D.r_theta - D.theta_r ∧ 1 < D.r_theta / D.theta_r := by
  refine ⟨D.derived_collision_rh_analytic_buffer_layer_theta_r_pos,
    D.derived_collision_rh_analytic_buffer_layer_theta_r_lt_r_theta, ?_, ?_⟩
  · linarith [D.derived_collision_rh_analytic_buffer_layer_theta_r_lt_r_theta]
  · have hbuffer : 0 < D.r_theta - D.theta_r := by
      linarith [D.derived_collision_rh_analytic_buffer_layer_theta_r_lt_r_theta]
    have htheta_ne : D.theta_r ≠ 0 := ne_of_gt D.derived_collision_rh_analytic_buffer_layer_theta_r_pos
    have hbuffer_div_pos : 0 < (D.r_theta - D.theta_r) / D.theta_r := by
      exact div_pos hbuffer D.derived_collision_rh_analytic_buffer_layer_theta_r_pos
    have hratio :
        D.r_theta / D.theta_r = 1 + (D.r_theta - D.theta_r) / D.theta_r := by
      field_simp [htheta_ne]
      ring
    nlinarith [hbuffer_div_pos, hratio]

end Omega.DerivedConsequences
