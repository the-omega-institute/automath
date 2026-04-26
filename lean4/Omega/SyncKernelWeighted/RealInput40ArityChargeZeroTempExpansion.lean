import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40ArityChargeDetClosed

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The constant term in the Puiseux ansatz
`Λ(q) = √(3q) + a₀ + a₁ q^{-1/2} + a₂ q^{-1} + ···`. -/
def real_input_40_arity_charge_zero_temp_expansion_a0 : ℚ :=
  2 / 3

/-- The `q^{-1/2}` coefficient in the same Puiseux ansatz. -/
def real_input_40_arity_charge_zero_temp_expansion_a1 : ℚ :=
  0

/-- The `q^{-1}` coefficient in the same Puiseux ansatz. -/
def real_input_40_arity_charge_zero_temp_expansion_a2 : ℚ :=
  56 / 81

/-- First reduced coefficient after substituting the Puiseux ansatz into `P₇`. -/
def real_input_40_arity_charge_zero_temp_expansion_coeff_t1 (a0 : ℚ) : ℚ :=
  6 * (3 * a0 - 2)

/-- Second reduced coefficient after setting `a₁ = 0`. -/
def real_input_40_arity_charge_zero_temp_expansion_coeff_t2 (a0 : ℚ) : ℚ :=
  57 * a0 ^ 2 - 44 * a0 + 4

/-- Third reduced coefficient after setting `a₁ = 0`. -/
def real_input_40_arity_charge_zero_temp_expansion_coeff_t3 (a0 a2 : ℚ) : ℚ :=
  171 * a0 ^ 3 - 166 * a0 ^ 2 + 22 * a0 + 18 * a2 - 4

/-- The first pressure correction coming from the constant term of `λ(e^θ)`. -/
def real_input_40_arity_charge_zero_temp_expansion_pressure_half_term : ℝ :=
  (real_input_40_arity_charge_zero_temp_expansion_a0 : ℝ) / Real.sqrt 3

/-- The `e^{-θ}` coefficient produced by the quadratic term in `log (1 + u)`. -/
def real_input_40_arity_charge_zero_temp_expansion_pressure_one_term : ℝ :=
  -((real_input_40_arity_charge_zero_temp_expansion_a0 : ℝ) / Real.sqrt 3) ^ 2 / 2

/-- Concrete coefficient-comparison certificate for the zero-temperature Puiseux branch. -/
def real_input_40_arity_charge_zero_temp_expansion_statement : Prop :=
  real_input_40_arity_charge_zero_temp_expansion_coeff_t1
      real_input_40_arity_charge_zero_temp_expansion_a0 = 0 ∧
    real_input_40_arity_charge_zero_temp_expansion_coeff_t2
      real_input_40_arity_charge_zero_temp_expansion_a0 = 0 ∧
    real_input_40_arity_charge_zero_temp_expansion_coeff_t3
      real_input_40_arity_charge_zero_temp_expansion_a0
      real_input_40_arity_charge_zero_temp_expansion_a2 = 0 ∧
    real_input_40_arity_charge_zero_temp_expansion_pressure_half_term = 2 / (3 * Real.sqrt 3) ∧
    real_input_40_arity_charge_zero_temp_expansion_pressure_one_term = -(2 : ℝ) / 27

private lemma real_input_40_arity_charge_zero_temp_expansion_sqrt3_sq :
    (Real.sqrt 3) ^ 2 = 3 := by
  nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by positivity)]

/-- Paper label: `prop:real-input-40-arity-charge-zero-temp-expansion`. The first three reduced
coefficient equations of the `q → +∞` Puiseux branch are solved by `a₀ = 2/3`, `a₁ = 0`,
`a₂ = 56/81`, and the corresponding pressure corrections are
`2 / (3 √3)` at order `e^{-θ/2}` and `-2/27` at order `e^{-θ}`. -/
theorem paper_real_input_40_arity_charge_zero_temp_expansion :
    real_input_40_arity_charge_zero_temp_expansion_statement := by
  constructor
  · norm_num [real_input_40_arity_charge_zero_temp_expansion_coeff_t1,
      real_input_40_arity_charge_zero_temp_expansion_a0]
  constructor
  · norm_num [real_input_40_arity_charge_zero_temp_expansion_coeff_t2,
      real_input_40_arity_charge_zero_temp_expansion_a0]
  constructor
  · norm_num [real_input_40_arity_charge_zero_temp_expansion_coeff_t3,
      real_input_40_arity_charge_zero_temp_expansion_a0,
      real_input_40_arity_charge_zero_temp_expansion_a2]
  constructor
  · have hsqrt3 : (Real.sqrt 3 : ℝ) ≠ 0 := by positivity
    calc
      real_input_40_arity_charge_zero_temp_expansion_pressure_half_term
          = ((2 : ℝ) / 3) / Real.sqrt 3 := by
              norm_num [real_input_40_arity_charge_zero_temp_expansion_pressure_half_term,
                real_input_40_arity_charge_zero_temp_expansion_a0]
      _ = 2 / (3 * Real.sqrt 3) := by
            field_simp [hsqrt3]
  · have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
    have hsquare :
        ((((2 : ℝ) / 3) / Real.sqrt 3) ^ 2) = 4 / 27 := by
      field_simp [hsqrt3]
      nlinarith [real_input_40_arity_charge_zero_temp_expansion_sqrt3_sq]
    calc
      real_input_40_arity_charge_zero_temp_expansion_pressure_one_term
          = -((((2 : ℝ) / 3) / Real.sqrt 3) ^ 2) / 2 := by
              norm_num [real_input_40_arity_charge_zero_temp_expansion_pressure_one_term,
                real_input_40_arity_charge_zero_temp_expansion_a0]
      _ = -(4 / 27 : ℝ) / 2 := by rw [hsquare]
      _ = -(2 : ℝ) / 27 := by norm_num

end

end Omega.SyncKernelWeighted
