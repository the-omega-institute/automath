import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.UnitCirclePhaseArithmetic.UnitCircleComovingRadialBitComplexity
import Omega.UnitCirclePhaseArithmetic.UnitCirclePhaseLogConditionNumbers

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Concrete Jacobian ledger behind the phase-difference entropy identity. -/
def unit_circle_phase_diff_entropy_ledger_statement : Prop :=
  ∀ x : ℝ,
    phasePrecisionPotential x =
        -Real.log |deriv unit_circle_comoving_radial_bit_complexity_compactified x| ∧
      phasePrecisionPotential x = Real.log Real.pi + Real.log (1 + x ^ 2)

lemma unit_circle_phase_diff_entropy_ledger_jacobian (x : ℝ) :
    phasePrecisionPotential x =
      -Real.log |deriv unit_circle_comoving_radial_bit_complexity_compactified x| := by
  have hderiv := unit_circle_comoving_radial_bit_complexity_compactified_deriv x
  have harg_pos : 0 < Real.pi * (1 + x ^ 2) := by positivity
  have harg_ne : Real.pi * (1 + x ^ 2) ≠ 0 := ne_of_gt harg_pos
  have habs :
      |1 / (Real.pi * (1 + x ^ 2))| = 1 / (Real.pi * (1 + x ^ 2)) := by
    exact abs_of_nonneg (by positivity)
  rw [hderiv, habs]
  calc
    phasePrecisionPotential x = Real.log (Real.pi * (1 + x ^ 2)) := by
      rw [Real.log_mul Real.pi_ne_zero (by positivity : (1 + x ^ 2) ≠ 0)]
      simp [phasePrecisionPotential]
    _ = -Real.log ((Real.pi * (1 + x ^ 2))⁻¹) := by
      rw [Real.log_inv]
      ring
    _ = -Real.log (1 / (Real.pi * (1 + x ^ 2))) := by simp [one_div]

/-- The Jacobian term for `u = arctan(x) / π` is exactly `log π + log (1 + x²)`. -/
theorem unit_circle_phase_diff_entropy_ledger_certified :
    unit_circle_phase_diff_entropy_ledger_statement := by
  intro x
  refine ⟨unit_circle_phase_diff_entropy_ledger_jacobian x, ?_⟩
  simp [phasePrecisionPotential]

/-- Paper label: `prop:unit-circle-phase-diff-entropy-ledger`. -/
def paper_unit_circle_phase_diff_entropy_ledger : Prop := by
  exact unit_circle_phase_diff_entropy_ledger_statement

end

end Omega.UnitCirclePhaseArithmetic
