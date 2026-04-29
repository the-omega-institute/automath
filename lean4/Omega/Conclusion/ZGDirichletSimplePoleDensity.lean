import Omega.Zeta.XiTimePart62aZGZetaNormalizedDensityLimit
import Omega.Zeta.XiTimePart62dhZGDirichletDensityResidue

open Filter Topology

namespace Omega.Conclusion

open Omega.Zeta

/-- Concrete wrapper data for the ZG Dirichlet simple-pole density theorem. -/
structure conclusion_zg_dirichlet_simple_pole_density_data where
  conclusion_zg_dirichlet_simple_pole_density_witness :
    Omega.Zeta.XiZGAbelResidueLogDensityWitness

namespace conclusion_zg_dirichlet_simple_pole_density_data

def statement (D : conclusion_zg_dirichlet_simple_pole_density_data) : Prop :=
  Omega.Zeta.xiTimePart62aZGSimplePoleDensityResidueStatement
      D.conclusion_zg_dirichlet_simple_pole_density_witness ∧
    Tendsto
      (Omega.Zeta.xi_time_part62a_zg_zeta_normalized_density_limit_ratio
        D.conclusion_zg_dirichlet_simple_pole_density_witness)
      (𝓝[>] (1 : ℝ))
      (𝓝 D.conclusion_zg_dirichlet_simple_pole_density_witness.analytic.deltaZG) ∧
    D.conclusion_zg_dirichlet_simple_pole_density_witness.absoluteConvergenceCriticalLine

end conclusion_zg_dirichlet_simple_pole_density_data

/-- Paper label: `thm:conclusion-zg-dirichlet-simple-pole-density`. -/
theorem paper_conclusion_zg_dirichlet_simple_pole_density
    (D : conclusion_zg_dirichlet_simple_pole_density_data) : D.statement := by
  rcases Omega.Zeta.paper_xi_time_part62a_zg_simple_pole_density_residue
      D.conclusion_zg_dirichlet_simple_pole_density_witness with
    ⟨hresidue, hharmonic⟩
  rcases Omega.Zeta.paper_xi_time_part62a_zg_zeta_normalized_density_limit
      D.conclusion_zg_dirichlet_simple_pole_density_witness with
    ⟨_, hlimit⟩
  rcases Omega.Zeta.paper_xi_zg_abel_residue_log_density
      D.conclusion_zg_dirichlet_simple_pole_density_witness with
    ⟨_, _, hcritical⟩
  exact ⟨⟨hresidue, hharmonic⟩, hlimit, hcritical⟩

end Omega.Conclusion
