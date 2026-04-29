import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-leyang-jordan-logshift`. -/
theorem paper_xi_leyang_jordan_logshift
    (jordanPowerExpansion dominantTwoBranchExpansion logshiftFormula
      nonremovableJordanCoefficient : Prop)
    (hPow : jordanPowerExpansion)
    (hDom : jordanPowerExpansion -> dominantTwoBranchExpansion)
    (hShift : dominantTwoBranchExpansion -> logshiftFormula)
    (hCoeff : logshiftFormula -> nonremovableJordanCoefficient) :
    jordanPowerExpansion ∧ dominantTwoBranchExpansion ∧ logshiftFormula ∧
      nonremovableJordanCoefficient := by
  exact ⟨hPow, hDom hPow, hShift (hDom hPow), hCoeff (hShift (hDom hPow))⟩

end Omega.Zeta
