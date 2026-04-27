import Omega.GU.JoukowskyGodelLeadingCoeffRigidity

namespace Omega.Zeta

/-- Paper label: `thm:xi-jg-transport-resultant-leading-rigidity`. -/
theorem paper_xi_jg_transport_resultant_leading_rigidity {K : Type*} [Field K]
    (D : Omega.GU.JoukowskyGodelTransportData K) : D.leadingCoeffRigidity := by
  exact Omega.GU.paper_group_jg_lc_rigidity D

end Omega.Zeta
