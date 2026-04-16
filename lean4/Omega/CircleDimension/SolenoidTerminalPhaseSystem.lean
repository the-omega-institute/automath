import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local wrapper for the generic monotheticity argument on an `S`-solenoid. It records
the countable family of nontrivial character kernels, the characterization of generators as the
complement of their union, the smallness properties of each kernel, and the deductions of
monotheticity, dense `G_δ`, and full Haar measure from those inputs. -/
structure SSolenoidGenericMonotheticData where
  nontrivialCharacterKernels : Prop
  generatorsAreComplementOfKernelUnion : Prop
  kernelsProper : Prop
  kernelsClosed : Prop
  kernelsNowhereDense : Prop
  kernelsNull : Prop
  countableKernelFamily : Prop
  monothetic : Prop
  generatorsDenseGdelta : Prop
  generatorsFullMeasure : Prop
  nontrivialCharacterKernels_h : nontrivialCharacterKernels
  generatorsAreComplementOfKernelUnion_h : generatorsAreComplementOfKernelUnion
  kernelsProper_h : kernelsProper
  kernelsClosed_h : kernelsClosed
  kernelsNowhereDense_h : kernelsNowhereDense
  kernelsNull_h : kernelsNull
  countableKernelFamily_h : countableKernelFamily
  deriveMonothetic :
    generatorsAreComplementOfKernelUnion → kernelsProper → monothetic
  deriveDenseGdelta :
    generatorsAreComplementOfKernelUnion → kernelsClosed → kernelsNowhereDense →
      countableKernelFamily → generatorsDenseGdelta
  deriveFullMeasure :
    generatorsAreComplementOfKernelUnion → kernelsNull → countableKernelFamily →
      generatorsFullMeasure

/-- The generator set is the complement of the countable union of nontrivial character kernels. -/
theorem SSolenoidGenericMonotheticData.generators_characterization
    (D : SSolenoidGenericMonotheticData) :
    D.generatorsAreComplementOfKernelUnion :=
  D.generatorsAreComplementOfKernelUnion_h

/-- Each nontrivial character kernel is small enough to support both the Baire-category and Haar
measure arguments used in the generic monotheticity proof. -/
theorem SSolenoidGenericMonotheticData.kernel_smallness
    (D : SSolenoidGenericMonotheticData) :
    D.kernelsProper ∧ D.kernelsClosed ∧ D.kernelsNowhereDense ∧ D.kernelsNull ∧
      D.countableKernelFamily := by
  exact ⟨D.kernelsProper_h, D.kernelsClosed_h, D.kernelsNowhereDense_h, D.kernelsNull_h,
    D.countableKernelFamily_h⟩

/-- Paper-facing wrapper for the generic monotheticity package of an `S`-solenoid.
    thm:cdim-s-solenoid-generic-monothetic -/
theorem paper_cdim_s_solenoid_generic_monothetic (D : SSolenoidGenericMonotheticData) :
    D.monothetic ∧ D.generatorsDenseGdelta ∧ D.generatorsFullMeasure := by
  have hGen : D.generatorsAreComplementOfKernelUnion := D.generators_characterization
  rcases D.kernel_smallness with ⟨hProper, hClosed, hNowhereDense, hNull, hCountable⟩
  exact ⟨D.deriveMonothetic hGen hProper, D.deriveDenseGdelta hGen hClosed hNowhereDense hCountable,
    D.deriveFullMeasure hGen hNull hCountable⟩

end Omega.CircleDimension
