import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40AlphaMax
import Omega.SyncKernelWeighted.RealInput40ArityChargeDerivativeQ0
import Omega.SyncKernelWeighted.RealInput40ArityChargeZeroTempExpansion
import Omega.SyncKernelWeighted.RealInput40GroundEntropy

namespace Omega.SyncKernelWeighted

open Filter

noncomputable section

/-- Concrete endpoint data for the real-input-40 arity-charge pressure curve: the left endpoint is
anchored by a chosen `q = 0` Perron root `κ`, while the right endpoint reuses the existing
zero-temperature and ground-state packages. -/
structure real_input_40_arity_charge_endpoints_data where
  kappa : ℝ
  kappa_root : kappa ^ 4 - kappa ^ 3 - 1 = 0
  kappa_gt_one : 1 < kappa

namespace real_input_40_arity_charge_endpoints_data

/-- Left endpoint package: the zero-charge specialization vanishes at `κ`, the root is simple, and
its implicit slope is the audited closed form. -/
def left_endpoint_pressure (D : real_input_40_arity_charge_endpoints_data) : Prop :=
  realInput40ArityChargeP7Q0 D.kappa = 0 ∧
    realInput40ArityChargeP7LambdaPartialAtQ0 D.kappa ≠ 0 ∧
    realInput40ArityChargeImplicitSlopeQ0 D.kappa =
      (2 * D.kappa ^ 3 + D.kappa ^ 2 + 8 * D.kappa - 2) / (D.kappa * (4 * D.kappa - 3))

/-- Right endpoint package: the Puiseux expansion is already solved, and the affine pressure model
has asymptotic intercept `log 3 / 2` coming from the ground-state factor `sqrt 3`. -/
def right_endpoint_pressure (_D : real_input_40_arity_charge_endpoints_data) : Prop :=
  real_input_40_arity_charge_zero_temp_expansion_statement ∧
    Tendsto (fun θ : ℝ => realInput40GroundPressure (Real.sqrt 3) θ - θ / 2) atTop
      (nhds (Real.log 3 / 2))

/-- The maximal charge density extracted from the audited endpoint loop mean. -/
def max_charge_density (_D : real_input_40_arity_charge_endpoints_data) : ℝ :=
  real_input_40_alpha_max_value

end real_input_40_arity_charge_endpoints_data

open real_input_40_arity_charge_endpoints_data

/-- Paper label: `prop:real-input-40-arity-charge-endpoints`. The `q = 0` branch is controlled by
the explicit zero-charge root package, the `q → +∞` endpoint is read off from the zero-temperature
expansion together with the affine ground-state pressure `θ / 2 + log 3 / 2`, and the maximal
charge density is `1 / 2`. -/
theorem paper_real_input_40_arity_charge_endpoints
    (D : real_input_40_arity_charge_endpoints_data) :
    D.left_endpoint_pressure ∧ D.right_endpoint_pressure ∧ D.max_charge_density = (1 / 2 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact paper_real_input_40_arity_charge_derivative_q0 D.kappa_root D.kappa_gt_one
  · refine ⟨paper_real_input_40_arity_charge_zero_temp_expansion, ?_⟩
    have hsqrt3_nonneg : 0 ≤ (Real.sqrt 3 : ℝ) := by
      positivity
    have hsqrt3_sq : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by positivity)]
    have hsqrt3_gt_one : 1 < (Real.sqrt 3 : ℝ) := by
      nlinarith
    rcases paper_real_input_40_ground_entropy (Real.sqrt 3) hsqrt3_gt_one with ⟨_, hTendsto, _⟩
    have hlog_sqrt3 : realInput40GroundEntropy (Real.sqrt 3) = Real.log 3 / 2 := by
      unfold realInput40GroundEntropy
      rw [Real.log_sqrt (show 0 ≤ (3 : ℝ) by positivity)]
    simpa [right_endpoint_pressure, hlog_sqrt3] using hTendsto
  · rcases paper_real_input_40_alpha_max with ⟨_, _, _, _, hmax⟩
    simpa [max_charge_density] using hmax

end

end Omega.SyncKernelWeighted
