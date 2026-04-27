import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Concrete package for the real-input `40` atomic Abel shift.  The pressure branch, the
beta-shift, the first two audited derivative functions, and the equilibrium constants are stored
as real-valued data. -/
structure xi_real_input40_atomic_abel_shift_differential_tower_data where
  pressure : ℝ → ℝ
  pressureDeriv : ℝ → ℝ
  pressureSecondDeriv : ℝ → ℝ
  betaShift : ℝ → ℝ
  betaShiftDeriv : ℝ → ℝ
  betaShiftSecondDeriv : ℝ → ℝ
  lambda : ℝ → ℝ
  pressureDerivAtZeroValue : ℝ
  pressureSecondDerivAtZeroValue : ℝ
  lambdaOneValue : ℝ
  atomic_factor_thermodynamic_invariance :
    ∀ θ : ℝ, betaShift θ = Real.exp (θ - 2 * pressure θ)
  beta_shift_first_derivative_identity :
    ∀ θ : ℝ, betaShiftDeriv θ = betaShift θ * (1 - 2 * pressureDeriv θ)
  beta_shift_second_derivative_identity :
    ∀ θ : ℝ,
      betaShiftSecondDeriv θ =
        betaShift θ * ((1 - 2 * pressureDeriv θ) ^ 2 - 2 * pressureSecondDeriv θ)
  pressure_derivative_zero : pressureDeriv 0 = pressureDerivAtZeroValue
  pressure_second_derivative_zero : pressureSecondDeriv 0 = pressureSecondDerivAtZeroValue
  lambda_one_value : lambda 1 = lambdaOneValue

namespace xi_real_input40_atomic_abel_shift_differential_tower_data

/-- The atomic Abel shift identity and its first two differential consequences, including the
audited constants at the equilibrium point `theta = 0`. -/
def atomic_shift_identity_and_differential_tower
    (D : xi_real_input40_atomic_abel_shift_differential_tower_data) : Prop :=
  (∀ θ : ℝ, D.betaShift θ = Real.exp (θ - 2 * D.pressure θ)) ∧
    (∀ θ : ℝ, D.betaShiftDeriv θ = D.betaShift θ * (1 - 2 * D.pressureDeriv θ)) ∧
      (∀ θ : ℝ,
        D.betaShiftSecondDeriv θ =
          D.betaShift θ * ((1 - 2 * D.pressureDeriv θ) ^ 2 -
            2 * D.pressureSecondDeriv θ)) ∧
        D.betaShift 0 = Real.exp (0 - 2 * D.pressure 0) ∧
          D.betaShiftDeriv 0 =
            D.betaShift 0 * (1 - 2 * D.pressureDerivAtZeroValue) ∧
            D.betaShiftSecondDeriv 0 =
              D.betaShift 0 * ((1 - 2 * D.pressureDerivAtZeroValue) ^ 2 -
                2 * D.pressureSecondDerivAtZeroValue) ∧
              D.lambda 1 = D.lambdaOneValue

end xi_real_input40_atomic_abel_shift_differential_tower_data

/-- Paper label: `cor:xi-real-input40-atomic-abel-shift-differential-tower`. -/
theorem paper_xi_real_input40_atomic_abel_shift_differential_tower
    (D : xi_real_input40_atomic_abel_shift_differential_tower_data) :
    D.atomic_shift_identity_and_differential_tower := by
  refine ⟨D.atomic_factor_thermodynamic_invariance, D.beta_shift_first_derivative_identity,
    D.beta_shift_second_derivative_identity, ?_, ?_, ?_, D.lambda_one_value⟩
  · exact D.atomic_factor_thermodynamic_invariance 0
  · calc
      D.betaShiftDeriv 0 = D.betaShift 0 * (1 - 2 * D.pressureDeriv 0) :=
        D.beta_shift_first_derivative_identity 0
      _ = D.betaShift 0 * (1 - 2 * D.pressureDerivAtZeroValue) := by
        rw [D.pressure_derivative_zero]
  · calc
      D.betaShiftSecondDeriv 0 =
          D.betaShift 0 * ((1 - 2 * D.pressureDeriv 0) ^ 2 -
            2 * D.pressureSecondDeriv 0) :=
        D.beta_shift_second_derivative_identity 0
      _ =
          D.betaShift 0 * ((1 - 2 * D.pressureDerivAtZeroValue) ^ 2 -
            2 * D.pressureSecondDerivAtZeroValue) := by
        rw [D.pressure_derivative_zero, D.pressure_second_derivative_zero]

end Omega.SyncKernelRealInput
