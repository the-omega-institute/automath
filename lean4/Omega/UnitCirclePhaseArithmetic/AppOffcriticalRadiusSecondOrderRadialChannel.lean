import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppOffcriticalRadiusHighHeight

open Filter

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- A concrete endpoint-depth proxy equivalent to the high-height area-phase scale. -/
def app_offcritical_radius_second_order_radial_channel_delta_gamma (γ : ℝ) : ℝ :=
  1 / (Real.pi * γ)

/-- Paper-facing second-order radial-channel asymptotics written in the concrete proxy
`δ_γ = 1 / (π γ)`. -/
def app_offcritical_radius_second_order_radial_channel_statement : Prop :=
  ∀ δ : ℝ, 0 < δ →
    Tendsto
        (fun γ : ℝ =>
          Omega.Zeta.appOffcriticalBoundaryDepth γ δ /
            (app_offcritical_radius_second_order_radial_channel_delta_gamma γ) ^ 2)
        atTop
        (nhds (4 * δ * Real.pi ^ 2)) ∧
      Tendsto
        (fun γ : ℝ =>
          (1 - Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ)) /
            (app_offcritical_radius_second_order_radial_channel_delta_gamma γ) ^ 2)
        atTop
        (nhds (2 * δ * Real.pi ^ 2))

/-- Paper label: `cor:app-offcritical-radius-second-order-radial-channel`. -/
theorem paper_app_offcritical_radius_second_order_radial_channel :
    app_offcritical_radius_second_order_radial_channel_statement := by
  intro δ hδ
  rcases paper_app_offcritical_radius_high_height δ hδ with ⟨hdepth, hradial⟩
  have hdepth_scaled :
      Tendsto
        (fun γ : ℝ =>
          Real.pi ^ 2 * (γ ^ 2 * Omega.Zeta.appOffcriticalBoundaryDepth γ δ))
        atTop
        (nhds (Real.pi ^ 2 * (4 * δ))) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.pi ^ 2) atTop (nhds (Real.pi ^ 2))).mul
      hdepth
  have hradial_scaled :
      Tendsto
        (fun γ : ℝ =>
          Real.pi ^ 2 * (γ ^ 2 * (1 - Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ))))
        atTop
        (nhds (Real.pi ^ 2 * (2 * δ))) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.pi ^ 2) atTop (nhds (Real.pi ^ 2))).mul
      hradial
  have hdepth_eq :
      ∀ γ : ℝ,
        Omega.Zeta.appOffcriticalBoundaryDepth γ δ /
            (app_offcritical_radius_second_order_radial_channel_delta_gamma γ) ^ 2 =
          Real.pi ^ 2 * (γ ^ 2 * Omega.Zeta.appOffcriticalBoundaryDepth γ δ) := by
    intro γ
    have hsquare :
        (app_offcritical_radius_second_order_radial_channel_delta_gamma γ) ^ 2 =
          (Real.pi ^ 2 * γ ^ 2)⁻¹ := by
      simp [app_offcritical_radius_second_order_radial_channel_delta_gamma, div_eq_mul_inv, pow_two,
        mul_left_comm, mul_comm]
    calc
      Omega.Zeta.appOffcriticalBoundaryDepth γ δ /
          (app_offcritical_radius_second_order_radial_channel_delta_gamma γ) ^ 2 =
        Omega.Zeta.appOffcriticalBoundaryDepth γ δ * (Real.pi ^ 2 * γ ^ 2) := by
          rw [hsquare, div_eq_mul_inv, inv_inv]
      _ = Real.pi ^ 2 * (γ ^ 2 * Omega.Zeta.appOffcriticalBoundaryDepth γ δ) := by
          ring
  have hradial_eq :
      ∀ γ : ℝ,
        (1 - Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ)) /
            (app_offcritical_radius_second_order_radial_channel_delta_gamma γ) ^ 2 =
          Real.pi ^ 2 * (γ ^ 2 * (1 - Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ))) := by
    intro γ
    have hsquare :
        (app_offcritical_radius_second_order_radial_channel_delta_gamma γ) ^ 2 =
          (Real.pi ^ 2 * γ ^ 2)⁻¹ := by
      simp [app_offcritical_radius_second_order_radial_channel_delta_gamma, div_eq_mul_inv, pow_two,
        mul_left_comm, mul_comm]
    calc
      (1 - Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ)) /
          (app_offcritical_radius_second_order_radial_channel_delta_gamma γ) ^ 2 =
        (1 - Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ)) * (Real.pi ^ 2 * γ ^ 2) := by
          rw [hsquare, div_eq_mul_inv, inv_inv]
      _ = Real.pi ^ 2 * (γ ^ 2 * (1 - Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ))) := by
          ring
  refine ⟨?_, ?_⟩
  · convert hdepth_scaled using 1
    · funext γ
      exact hdepth_eq γ
    · ring
  · convert hradial_scaled using 1
    · funext γ
      exact hradial_eq γ
    · ring

end

end Omega.UnitCirclePhaseArithmetic
