import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-rh-cohn-derivative`. -/
theorem paper_xi_rh_cohn_derivative
    (unitCircleRoots selfInversive derivativeDiskRoots xiRH : Prop)
    (hcohn : unitCircleRoots ↔ selfInversive ∧ derivativeDiskRoots)
    (hrh : xiRH ↔ unitCircleRoots) :
    xiRH ↔ selfInversive ∧ derivativeDiskRoots := by
  exact hrh.trans hcohn

end Omega.Zeta
