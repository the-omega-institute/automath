import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Omega.Zeta

/-- Paper label: `cor:selfdual-index-vanish-implies-dbl0`. -/
theorem paper_selfdual_index_vanish_implies_dbl0 (F : Type*)
    (finiteInnerScattering windVanish windingEqualsBlaschkeDegree blaschkeDefectZero : Prop)
    (hwind : finiteInnerScattering → windVanish)
    (hdegree : finiteInnerScattering → windVanish → windingEqualsBlaschkeDegree)
    (hzero : windingEqualsBlaschkeDegree → blaschkeDefectZero) :
    finiteInnerScattering → blaschkeDefectZero := by
  intro hfinite
  exact hzero (hdegree hfinite (hwind hfinite))

end Omega.Zeta
