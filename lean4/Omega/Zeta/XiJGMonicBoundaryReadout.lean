import Omega.GU.JoukowskyGodelLeadingCoeffRigidity

namespace Omega.Zeta

/-- Paper label: `cor:xi-jg-monic-boundary-readout`. In the monic case `a_n = 1`, the existing
Joukowsky-Godel leading-coefficient rigidity theorem rewrites the transported leading coefficient
as the constant term. -/
theorem paper_xi_jg_monic_boundary_readout {K : Type*} [Field K]
    (D : Omega.GU.JoukowskyGodelTransportData K) (hmonic : D.a_n = 1) :
    D.transportLeadingCoeff = D.a_0 := by
  have hRigid := Omega.GU.paper_group_jg_lc_rigidity D
  dsimp [Omega.GU.JoukowskyGodelTransportData.leadingCoeffRigidity] at hRigid
  simpa [hmonic] using hRigid

end Omega.Zeta
