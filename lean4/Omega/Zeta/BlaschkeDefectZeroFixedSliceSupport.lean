import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Omega.Zeta

/-- Paper label: `thm:blaschke-defect-zero-fixed-slice-support`. -/
theorem paper_blaschke_defect_zero_fixed_slice_support (F : Type*)
    (boundedType selfDual defectZero noDiskZeros noExteriorZeros fixedSliceSupport : Prop)
    (hDisk : boundedType → defectZero → noDiskZeros)
    (hExterior : selfDual → noDiskZeros → noExteriorZeros)
    (hSupport : noDiskZeros → noExteriorZeros → fixedSliceSupport) :
    boundedType → selfDual → defectZero → noDiskZeros ∧ noExteriorZeros ∧ fixedSliceSupport := by
  intro hBounded hSelfDual hDefectZero
  have hNoDisk : noDiskZeros := hDisk hBounded hDefectZero
  have hNoExterior : noExteriorZeros := hExterior hSelfDual hNoDisk
  exact ⟨hNoDisk, hNoExterior, hSupport hNoDisk hNoExterior⟩

end Omega.Zeta
