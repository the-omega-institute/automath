import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The endpoint arc obtained from the Cayley coordinate `t = tan (θ / 2)`. -/
def app_horizon_endpoint_window_mass_theta (ε : ℝ) : ℝ :=
  2 * Real.arctan ε

/-- First-order endpoint mass term. -/
def app_horizon_endpoint_window_mass_main_term (ε : ℝ) : ℝ :=
  ε * Real.log (1 / ε)

/-- Constant-order correction term. -/
def app_horizon_endpoint_window_mass_correction (ε : ℝ) : ℝ :=
  ε

/-- Concrete endpoint-window package: the endpoint arc has positive width below `π`, the logarithmic
mass term rewrites as `ε (-log ε)`, and adding the constant correction keeps the first-order model
nonnegative on the small-window range `0 < ε ≤ 1`. -/
def app_horizon_endpoint_window_mass_statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    0 < app_horizon_endpoint_window_mass_theta ε ∧
    app_horizon_endpoint_window_mass_theta ε < Real.pi ∧
    Real.log (1 / ε) = -Real.log ε ∧
    app_horizon_endpoint_window_mass_main_term ε +
        app_horizon_endpoint_window_mass_correction ε =
      ε * (-Real.log ε + 1) ∧
    0 ≤
      app_horizon_endpoint_window_mass_main_term ε +
        app_horizon_endpoint_window_mass_correction ε

/-- Paper label: `thm:app-horizon-endpoint-window-mass`. -/
theorem paper_app_horizon_endpoint_window_mass : app_horizon_endpoint_window_mass_statement := by
  intro ε hε hε_le_one
  have harctan_pos : 0 < Real.arctan ε := Real.arctan_pos.mpr hε
  have htheta_pos : 0 < app_horizon_endpoint_window_mass_theta ε := by
    dsimp [app_horizon_endpoint_window_mass_theta]
    positivity
  have htheta_lt : app_horizon_endpoint_window_mass_theta ε < Real.pi := by
    dsimp [app_horizon_endpoint_window_mass_theta]
    nlinarith [Real.arctan_lt_pi_div_two ε]
  have hlog_inv : Real.log (1 / ε) = -Real.log ε := by
    rw [one_div, Real.log_inv]
  have hlog_nonpos : Real.log ε ≤ 0 := Real.log_nonpos (le_of_lt hε) hε_le_one
  have hmass_eq :
      app_horizon_endpoint_window_mass_main_term ε +
          app_horizon_endpoint_window_mass_correction ε =
        ε * (-Real.log ε + 1) := by
    unfold app_horizon_endpoint_window_mass_main_term
    unfold app_horizon_endpoint_window_mass_correction
    rw [hlog_inv]
    ring
  have hfactor_nonneg : 0 ≤ -Real.log ε + 1 := by
    linarith
  have hmass_nonneg :
      0 ≤
        app_horizon_endpoint_window_mass_main_term ε +
          app_horizon_endpoint_window_mass_correction ε := by
    rw [hmass_eq]
    exact mul_nonneg hε.le hfactor_nonneg
  exact ⟨htheta_pos, htheta_lt, hlog_inv, hmass_eq, hmass_nonneg⟩

end

end Omega.UnitCirclePhaseArithmetic
