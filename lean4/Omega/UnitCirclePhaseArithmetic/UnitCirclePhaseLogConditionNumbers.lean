import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- The precision potential attached to the unit-circle phase chart. -/
noncomputable def phasePrecisionPotential (t : ℝ) : ℝ :=
  Real.log Real.pi + Real.log (1 + t ^ 2)

/-- The Jacobian ledger for unit-circle phase addition and multiplication is an exact potential
difference, with the multiplicative channel carrying the extra `log |x|`/`log |y|` factor. -/
theorem paper_unit_circle_phase_log_condition_numbers (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    |(1 + x ^ 2) / (1 + (x + y) ^ 2)| = (1 + x ^ 2) / (1 + (x + y) ^ 2) ∧
      |(1 + y ^ 2) / (1 + (x + y) ^ 2)| = (1 + y ^ 2) / (1 + (x + y) ^ 2) ∧
      |(|y| * (1 + x ^ 2) / (1 + x ^ 2 * y ^ 2))| = |y| * (1 + x ^ 2) / (1 + x ^ 2 * y ^ 2) ∧
      |(|x| * (1 + y ^ 2) / (1 + x ^ 2 * y ^ 2))| = |x| * (1 + y ^ 2) / (1 + x ^ 2 * y ^ 2) ∧
      Real.log ((1 + x ^ 2) / (1 + (x + y) ^ 2)) =
        phasePrecisionPotential x - phasePrecisionPotential (x + y) ∧
      Real.log ((1 + y ^ 2) / (1 + (x + y) ^ 2)) =
        phasePrecisionPotential y - phasePrecisionPotential (x + y) ∧
      Real.log (|y| * (1 + x ^ 2) / (1 + x ^ 2 * y ^ 2)) =
        Real.log |y| + phasePrecisionPotential x - phasePrecisionPotential (x * y) ∧
      Real.log (|x| * (1 + y ^ 2) / (1 + x ^ 2 * y ^ 2)) =
        Real.log |x| + phasePrecisionPotential y - phasePrecisionPotential (x * y) := by
  have hxx : 0 < 1 + x ^ 2 := by positivity
  have hyy : 0 < 1 + y ^ 2 := by positivity
  have hadd : 0 < 1 + (x + y) ^ 2 := by positivity
  have hmul : 0 < 1 + x ^ 2 * y ^ 2 := by positivity
  have hxy : 0 < |x| := abs_pos.mpr hx
  have hyy' : 0 < |y| := abs_pos.mpr hy
  refine ⟨
    abs_of_nonneg (div_nonneg (by positivity) hadd.le),
    abs_of_nonneg (div_nonneg (by positivity) hadd.le),
    abs_of_nonneg (div_nonneg (mul_nonneg hyy'.le (by positivity)) hmul.le),
    abs_of_nonneg (div_nonneg (mul_nonneg hxy.le (by positivity)) hmul.le),
    ?_, ?_, ?_, ?_⟩
  · calc
      Real.log ((1 + x ^ 2) / (1 + (x + y) ^ 2))
          = Real.log (1 + x ^ 2) - Real.log (1 + (x + y) ^ 2) := by
              rw [Real.log_div hxx.ne' hadd.ne']
      _ = phasePrecisionPotential x - phasePrecisionPotential (x + y) := by
            simp [phasePrecisionPotential]
  · calc
      Real.log ((1 + y ^ 2) / (1 + (x + y) ^ 2))
          = Real.log (1 + y ^ 2) - Real.log (1 + (x + y) ^ 2) := by
              rw [Real.log_div hyy.ne' hadd.ne']
      _ = phasePrecisionPotential y - phasePrecisionPotential (x + y) := by
            simp [phasePrecisionPotential]
  · calc
      Real.log (|y| * (1 + x ^ 2) / (1 + x ^ 2 * y ^ 2))
          = Real.log |y| + (Real.log (1 + x ^ 2) - Real.log (1 + x ^ 2 * y ^ 2)) := by
              rw [Real.log_div (mul_ne_zero hyy'.ne' hxx.ne') hmul.ne']
              rw [Real.log_mul hyy'.ne' hxx.ne']
              ring
      _ = Real.log |y| + phasePrecisionPotential x - phasePrecisionPotential (x * y) := by
            have hsq : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by ring
            simp [phasePrecisionPotential, hsq]
            ring
  · calc
      Real.log (|x| * (1 + y ^ 2) / (1 + x ^ 2 * y ^ 2))
          = Real.log |x| + (Real.log (1 + y ^ 2) - Real.log (1 + x ^ 2 * y ^ 2)) := by
              rw [Real.log_div (mul_ne_zero hxy.ne' hyy.ne') hmul.ne']
              rw [Real.log_mul hxy.ne' hyy.ne']
              ring
      _ = Real.log |x| + phasePrecisionPotential y - phasePrecisionPotential (x * y) := by
            have hsq : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by ring
            simp [phasePrecisionPotential, hsq]
            ring

end Omega.UnitCirclePhaseArithmetic
