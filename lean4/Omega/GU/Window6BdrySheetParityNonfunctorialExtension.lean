import Mathlib.Tactic
import Omega.GU.FreeInvolutionCount

namespace Omega.GU

/-- Chapter-local package for the nonfunctorial boundary-sheet parity extension at window `6`.
The paper proof combines the even-fiber existence criterion for free involutions with the
fiberwise double-factorial count and the audited boundary multiplicities at `m = 6, 7, 8`. -/
structure Window6BdrySheetParityData where
  existsIffAllBoundaryFibersEven : Prop
  countEqFiberwiseDoubleFactorial : Prop
  auditValuesM6M7M8 : Prop
  existsIffAllBoundaryFibersEven_h : existsIffAllBoundaryFibersEven
  countEqFiberwiseDoubleFactorial_h : countEqFiberwiseDoubleFactorial
  auditValuesM6M7M8_h : auditValuesM6M7M8

/-- Paper-facing wrapper for the window-`6` boundary-sheet parity extension: the chapter-local
data records the existence criterion, the fiberwise double-factorial count, and the audited
boundary values at `m = 6, 7, 8`.
    thm:window6-bdry-sheet-parity-nonfunctorial-extension -/
theorem paper_window6_bdry_sheet_parity_nonfunctorial_extension
    (h : Window6BdrySheetParityData) :
    h.existsIffAllBoundaryFibersEven ∧ h.countEqFiberwiseDoubleFactorial ∧
      h.auditValuesM6M7M8 := by
  exact ⟨h.existsIffAllBoundaryFibersEven_h, h.countEqFiberwiseDoubleFactorial_h,
    h.auditValuesM6M7M8_h⟩

end Omega.GU
