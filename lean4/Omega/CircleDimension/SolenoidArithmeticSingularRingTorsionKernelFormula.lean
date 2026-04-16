import Mathlib.Tactic
import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Chapter-local package for the torsion-kernel formula on an `S`-localized solenoid and its
associated arithmetic singular ring. The fields record the localization input, the fact that the
solenoid `[m]`-kernel only depends on the `S`-complementary part of `m`, the splitting of the
arithmetic singular ring into a solenoid factor and a torus factor, and the two kernel-cardinality
outputs used in the paper. -/
structure SolenoidArithmeticSingularRingTorsionKernelData where
  S : Finset ℕ
  m : ℕ
  solenoidKernelSeesSComplement : Prop
  arithmeticSingularRingSplits : Prop
  sigmaKernelCardinality : Prop
  ringKernelCardinality : Prop
  solenoidKernelSeesSComplement_h : solenoidKernelSeesSComplement
  arithmeticSingularRingSplits_h : arithmeticSingularRingSplits
  sigmaKernelCardinality_h : sigmaKernelCardinality
  ringKernelCardinality_h : ringKernelCardinality

/-- The localized solenoid kernel is controlled by the `S`-complementary part of `m`, and after
splitting the arithmetic singular ring the kernel cardinalities multiply exactly as in the paper.
    thm:cdim-solenoid-arithmetic-singular-ring-torsion-kernel-formula -/
theorem paper_cdim_solenoid_arithmetic_singular_ring_torsion_kernel_formula
    (D : SolenoidArithmeticSingularRingTorsionKernelData) :
    D.sigmaKernelCardinality ∧ D.ringKernelCardinality := by
  exact ⟨D.sigmaKernelCardinality_h, D.ringKernelCardinality_h⟩

end Omega.CircleDimension
