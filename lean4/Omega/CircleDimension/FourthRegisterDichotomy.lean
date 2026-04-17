import Omega.Zeta.FourthRegisterDichotomy

namespace Omega.CircleDimension

/-- Circle-dimension phrasing of the fourth-register dichotomy: an off-slice assertion either
extends through the unique radial register or collapses to a finite `NULL` witness, with no third
continuous escape path. -/
def cdimFourthRegisterDichotomy
    (offsliceAssertion explicitRadialExtension nullWitness noThirdPath : Prop) : Prop :=
  offsliceAssertion → (explicitRadialExtension ∨ nullWitness) ∧ noThirdPath

/-- Circle-dimension-local wrapper around the Xi/Zeta fourth-register dichotomy.
    cor:cdim-fourth-register-dichotomy -/
theorem paper_cdim_fourth_register_dichotomy
    (offsliceAssertion explicitRadialExtension nullWitness noThirdPath : Prop)
    (hSplit : offsliceAssertion → explicitRadialExtension ∨ nullWitness)
    (hNoThird : offsliceAssertion → noThirdPath) :
    cdimFourthRegisterDichotomy offsliceAssertion explicitRadialExtension nullWitness noThirdPath := by
  simpa [cdimFourthRegisterDichotomy] using
    Omega.Zeta.paper_xi_fourth_register_dichotomy
      offsliceAssertion explicitRadialExtension nullWitness noThirdPath hSplit hNoThird

end Omega.CircleDimension
