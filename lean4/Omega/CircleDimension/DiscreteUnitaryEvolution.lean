import Mathlib.Tactic
import Omega.CircleDimension.ReadableTimeWordOverlapPD

namespace Omega.CircleDimension

/-- Chapter-local wrapper for the discrete unitary evolution on the readable-time-word overlap
quotient. It reuses the positive-definite overlap package, records the abstract time-shift action
on readable words, and packages the three paper-facing outputs: descent to the quotient,
isometricity on the quotient Hilbert pre-space, and the unitary extension to the completion. -/
structure ReadableTimeWordUnitaryEvolutionData extends ReadableTimeWordOverlapPDData where
  timeShiftAction : Prop
  shiftPreservesNullClasses : Prop
  quotientInnerProduct : Prop
  descendsToQuotient : Prop
  isometricQuotientShift : Prop
  completionExtensionExists : Prop
  hasUnitaryExtension : Prop
  hasTimeShiftAction : timeShiftAction
  hasShiftPreservesNullClasses : shiftPreservesNullClasses
  hasQuotientInnerProduct : quotientInnerProduct
  deriveDescentToQuotient :
    timeShiftAction → pullbackPositiveDefinite → shiftPreservesNullClasses → descendsToQuotient
  deriveIsometricQuotientShift :
    quotientInnerProduct → descendsToQuotient → isometricQuotientShift
  deriveCompletionExtension :
    descendsToQuotient → isometricQuotientShift → completionExtensionExists
  deriveUnitaryExtension :
    completionExtensionExists → isometricQuotientShift → hasUnitaryExtension

/-- Paper-facing wrapper for the discrete unitary evolution induced by the readable-time-word
overlap kernel.
    thm:cdim-discrete-unitary-evolution -/
theorem paper_cdim_discrete_unitary_evolution (D : ReadableTimeWordUnitaryEvolutionData) :
    D.descendsToQuotient ∧ D.isometricQuotientShift ∧ D.hasUnitaryExtension := by
  have hPD : D.pullbackPositiveDefinite :=
    (paper_cdim_readable_time_word_overlap_pd D.toReadableTimeWordOverlapPDData).1
  have hDesc : D.descendsToQuotient :=
    D.deriveDescentToQuotient D.hasTimeShiftAction hPD D.hasShiftPreservesNullClasses
  have hIso : D.isometricQuotientShift :=
    D.deriveIsometricQuotientShift D.hasQuotientInnerProduct hDesc
  have hExtension : D.completionExtensionExists :=
    D.deriveCompletionExtension hDesc hIso
  exact ⟨hDesc, hIso, D.deriveUnitaryExtension hExtension hIso⟩

end Omega.CircleDimension
