import Omega.Zeta.XiZGAbelResidueLogDensity

namespace Omega.Zeta

/-- Concrete statement packaging the `s = 1` residue normalization together with the Abel-summed
logarithmic main term for the Zeckendorf--Gödel Dirichlet series.
    thm:xi-time-part62a-zg-simple-pole-density-residue -/
def xiTimePart62aZGSimplePoleDensityResidueStatement
    (W : XiZGAbelResidueLogDensityWitness) : Prop :=
  W.analytic.residueAtOne = W.analytic.deltaZG ∧ W.harmonicMainTerm

/-- Paper label: `thm:xi-time-part62a-zg-simple-pole-density-residue`. -/
theorem paper_xi_time_part62a_zg_simple_pole_density_residue
    (W : XiZGAbelResidueLogDensityWitness) :
    xiTimePart62aZGSimplePoleDensityResidueStatement W := by
  rcases paper_xi_zg_abel_residue_log_density W with ⟨habel, hharm, _⟩
  exact ⟨habel.1, hharm⟩

end Omega.Zeta
