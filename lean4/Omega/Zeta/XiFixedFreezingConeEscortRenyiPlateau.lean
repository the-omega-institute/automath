import Omega.Zeta.XiFixedFreezingEscortRenyiSpectrumCollapse

namespace Omega.Zeta

/-- Paper label: `thm:xi-fixed-freezing-cone-escort-renyi-plateau`. -/
theorem paper_xi_fixed_freezing_cone_escort_renyi_plateau
    (D : xi_fixed_freezing_escort_renyi_spectrum_collapse_data) :
    derivedFixedFreezingEntropyRateLimit D.order = derivedFixedFreezingGStar := by
  exact (paper_xi_fixed_freezing_escort_renyi_spectrum_collapse D).1

end Omega.Zeta
