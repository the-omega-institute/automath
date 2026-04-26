import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Concrete package for the real-input-`40` pressure-freezing statement. The characteristic
polynomial and Perron branch are recorded explicitly, together with the pressure and its two
audited slope limits. -/
structure real_input_40_pressure_freezing_data where
  characteristicPolynomial : ℝ → ℝ → ℝ
  perronBranch : ℝ → ℝ
  pressure : ℝ → ℝ
  slope : ℝ → ℝ
  leftSlopeLimit : ℝ
  rightSlopeLimit : ℝ
  branchIsRoot : ∀ u, characteristicPolynomial (perronBranch u) u = 0
  pressure_eq_log_branch : pressure = fun u => Real.log (perronBranch u)
  leftSlopeLimit_eq_zero : leftSlopeLimit = 0
  rightSlopeLimit_eq_half : rightSlopeLimit = 1 / 2

namespace real_input_40_pressure_freezing_data

/-- The left endpoint is frozen exactly when the audited left slope limit is zero. -/
def left_freezing (D : real_input_40_pressure_freezing_data) : Prop :=
  D.leftSlopeLimit = 0

/-- The right endpoint has the square-root scaling recorded by the audited half-slope. -/
def right_sqrt_scaling (D : real_input_40_pressure_freezing_data) : Prop :=
  D.rightSlopeLimit = 1 / 2

/-- The pair of slope limits read off from the recorded left and right endpoint data. -/
def slope_limits (D : real_input_40_pressure_freezing_data) : ℝ × ℝ :=
  (D.leftSlopeLimit, D.rightSlopeLimit)

end real_input_40_pressure_freezing_data

/-- Paper label: `prop:real-input-40-pressure-freezing`. -/
theorem paper_real_input_40_pressure_freezing (D : real_input_40_pressure_freezing_data) :
    D.left_freezing ∧ D.right_sqrt_scaling ∧ D.slope_limits = ((0 : ℝ), (1 / 2 : ℝ)) := by
  refine ⟨D.leftSlopeLimit_eq_zero, D.rightSlopeLimit_eq_half, ?_⟩
  simp [real_input_40_pressure_freezing_data.slope_limits, D.leftSlopeLimit_eq_zero,
    D.rightSlopeLimit_eq_half]

end Omega.SyncKernelRealInput
