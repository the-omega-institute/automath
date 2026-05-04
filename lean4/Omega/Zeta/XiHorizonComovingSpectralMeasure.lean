import Omega.Zeta.XiBasepointScanFiniteRankRKHS

namespace Omega.Zeta

/-- Paper label: `thm:xi-horizon-comoving-spectral-measure`. -/
theorem paper_xi_horizon_comoving_spectral_measure
    (D : Omega.Zeta.xi_basepoint_scan_finite_rank_rkhs_data) :
    D.positiveKernel ∧ D.diagonalMatchesProfile ∧ D.rkhsRank = D.kappa := by
  exact Omega.Zeta.paper_xi_basepoint_scan_finite_rank_rkhs D

end Omega.Zeta
