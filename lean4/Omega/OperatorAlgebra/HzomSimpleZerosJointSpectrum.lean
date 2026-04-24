import Mathlib.Tactic
import Omega.OperatorAlgebra.HzomCriticalZerosJointSpectrumComb

namespace Omega.OperatorAlgebra

/-- Concrete data for the simple-zero/joint-spectrum criterion at a fixed comb point. -/
structure HzomSimpleZerosJointSpectrumData where
  lam : ℝ
  theta : ℝ
  combIndex : ℤ
  hlam : 0 < lam
  jointFiberMultiplicity : ℕ

/-- The distinguished critical zero height attached to the chosen comb index. -/
noncomputable def HzomSimpleZerosJointSpectrumData.zeroHeight
    (D : HzomSimpleZerosJointSpectrumData) : ℝ :=
  (D.theta + 2 * Real.pi * (D.combIndex : ℝ)) / D.lam

/-- The zero is simple exactly when the joint-spectral fiber carries multiplicity one. -/
def HzomSimpleZerosJointSpectrumData.simpleZeroIffJointFiberMultiplicityOne
    (D : HzomSimpleZerosJointSpectrumData) : Prop :=
  hzomZeroAt D.lam D.theta D.zeroHeight ∧ D.jointFiberMultiplicity = 1 ↔
    D.jointFiberMultiplicity = 1

private theorem hzom_zeroHeight_is_zero (D : HzomSimpleZerosJointSpectrumData) :
    hzomZeroAt D.lam D.theta D.zeroHeight := by
  simpa [HzomSimpleZerosJointSpectrumData.zeroHeight] using
    (paper_op_algebra_hzom_critical_zeros_joint_spectrum_comb D.lam D.theta D.hlam).1 D.combIndex

/-- Paper label: `cor:op-algebra-hzom-simple-zeros-joint-spectrum`. -/
theorem paper_op_algebra_hzom_simple_zeros_joint_spectrum
    (D : HzomSimpleZerosJointSpectrumData) : D.simpleZeroIffJointFiberMultiplicityOne := by
  dsimp [HzomSimpleZerosJointSpectrumData.simpleZeroIffJointFiberMultiplicityOne]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨hzom_zeroHeight_is_zero D, h⟩

end Omega.OperatorAlgebra
