import Omega.Zeta.XiZGAbelResidueLogDensity

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part62dh-zg-dirichlet-density-residue`. -/
theorem paper_xi_time_part62dh_zg_dirichlet_density_residue
    (W : XiZGAbelResidueLogDensityWitness) :
    W.analytic.residueAtOne = W.analytic.deltaZG ∧
      0 < W.analytic.deltaZG ∧
      W.analytic.deltaZG < 1 := by
  rcases paper_xi_zg_abel_residue_log_density W with ⟨_, _, habs⟩
  exact habs

end Omega.Zeta
