import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- Cayley-coordinate point on the unit circle attached to the real phase parameter `x`. -/
def unitCirclePhaseW (x : Real) : Complex :=
  (1 + Complex.I * (x : Complex)) / (1 - Complex.I * (x : Complex))

/-- Truncated Hardy kernel in rational closed form.  The diagonal value is defined by continuity. -/
def unitCirclePhaseHardyKernel (N : Nat) (x y : Real) : Complex :=
  if _hxy : x = y then (N : Complex)
  else (1 - (unitCirclePhaseW x * star (unitCirclePhaseW y)) ^ N) /
    (1 - unitCirclePhaseW x * star (unitCirclePhaseW y))

lemma one_sub_I_mul_ne_zero (x : Real) : (1 - Complex.I * (x : Complex)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

lemma one_add_I_mul_ne_zero (x : Real) : (1 + Complex.I * (x : Complex)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

lemma unitCirclePhase_one_sub_mul_conj (x y : Real) :
    1 - unitCirclePhaseW x * star (unitCirclePhaseW y) =
      (2 * Complex.I * (y - x)) / ((1 - Complex.I * x) * (1 + Complex.I * y)) := by
  have hDen1 : (1 - Complex.I * (x : Complex)) ≠ 0 := one_sub_I_mul_ne_zero x
  have hDen2 : (1 + Complex.I * (y : Complex)) ≠ 0 := one_add_I_mul_ne_zero y
  simp [unitCirclePhaseW, div_eq_mul_inv]
  field_simp [hDen1, hDen2]
  ring

lemma unitCirclePhase_inv_one_sub_mul_conj (x y : Real) (hxy : x ≠ y) :
    1 / (1 - unitCirclePhaseW x * star (unitCirclePhaseW y)) =
      ((1 - Complex.I * x) * (1 + Complex.I * y)) / (2 * Complex.I * (y - x)) := by
  have hDen1 : (1 - Complex.I * (x : Complex)) ≠ 0 := one_sub_I_mul_ne_zero x
  have hDen2 : (1 + Complex.I * (y : Complex)) ≠ 0 := one_add_I_mul_ne_zero y
  have hSub : ((y - x : Real) : Complex) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hxy.symm
  rw [unitCirclePhase_one_sub_mul_conj]
  have hTwoI : (2 : Complex) * Complex.I ≠ 0 := by norm_num
  have hNum : (2 : Complex) * Complex.I * (↑(y - x) : Complex) ≠ 0 := mul_ne_zero hTwoI hSub
  field_simp [hDen1, hDen2, hSub, hNum]

/-- Paper label: `prop:unit-circle-phase-hardy-kernel-rational`. -/
theorem paper_unit_circle_phase_hardy_kernel_rational (N : Nat) (hN : 1 <= N) (x y : Real) :
    unitCirclePhaseHardyKernel N x y =
      (if _hxy : x = y then (N : Complex)
       else (1 - (unitCirclePhaseW x * star (unitCirclePhaseW y)) ^ N) /
         (1 - unitCirclePhaseW x * star (unitCirclePhaseW y))) ∧
    (x != y ->
      1 / (1 - unitCirclePhaseW x * star (unitCirclePhaseW y)) =
        ((1 - Complex.I * x) * (1 + Complex.I * y)) / (2 * Complex.I * (y - x))) := by
  let _ := hN
  constructor
  · simp [unitCirclePhaseHardyKernel]
  · intro hxy
    have hxy' : x ≠ y := by simpa using hxy
    exact unitCirclePhase_inv_one_sub_mul_conj x y hxy'

end

end Omega.UnitCirclePhaseArithmetic
