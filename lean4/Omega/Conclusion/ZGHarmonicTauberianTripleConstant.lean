import Omega.Zeta.XiTimePart62aZGZetaNormalizedDensityLimit

open Filter Topology

namespace Omega.Conclusion

open Omega.Zeta

theorem paper_conclusion_zg_harmonic_tauberian_triple_constant
    (W : Omega.Zeta.XiZGAbelResidueLogDensityWitness) :
    W.abelBoundaryLaw ∧ W.harmonicMainTerm ∧
      Tendsto (Omega.Zeta.xi_time_part62a_zg_zeta_normalized_density_limit_ratio W)
        (𝓝[>] (1 : ℝ)) (𝓝 W.analytic.deltaZG) := by
  rcases paper_xi_zg_abel_residue_log_density W with ⟨habel, hharm, _⟩
  rcases paper_xi_time_part62a_zg_zeta_normalized_density_limit W with ⟨_, hlimit⟩
  exact ⟨habel, hharm, hlimit⟩

end Omega.Conclusion
