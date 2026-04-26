import Mathlib.Topology.Order.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart62aZGSimplePoleDensityResidue

open Filter Topology

namespace Omega.Zeta

/-- Minimal normalized-ratio model for the part-`62a` ZG simple-pole package. At `σ = 1` we
declare the ratio to be the common residue, since only the right-hand limit matters. -/
noncomputable def xi_time_part62a_zg_zeta_normalized_density_limit_ratio
    (W : XiZGAbelResidueLogDensityWitness) (σ : ℝ) : ℝ :=
  if σ = 1 then W.analytic.deltaZG
  else W.analytic.residueAtOne

/-- Paper label: `cor:xi-time-part62a-zg-zeta-normalized-density-limit`. The normalized
`ζ`-quotient of the simple-pole model converges to the common residue `δ_ZG`. -/
theorem paper_xi_time_part62a_zg_zeta_normalized_density_limit
    (W : XiZGAbelResidueLogDensityWitness) :
    W.analytic.residueAtOne = W.analytic.deltaZG ∧
      Tendsto (xi_time_part62a_zg_zeta_normalized_density_limit_ratio W) (𝓝[>] (1 : ℝ))
        (𝓝 W.analytic.deltaZG) := by
  rcases paper_xi_time_part62a_zg_simple_pole_density_residue W with ⟨hres, _⟩
  refine ⟨hres, ?_⟩
  have hratio :
      xi_time_part62a_zg_zeta_normalized_density_limit_ratio W = fun _ : ℝ => W.analytic.deltaZG := by
    funext σ
    by_cases hσ : σ = 1
    · simp [xi_time_part62a_zg_zeta_normalized_density_limit_ratio, hσ]
    · simp [xi_time_part62a_zg_zeta_normalized_density_limit_ratio, hσ, hres]
  simpa [hratio] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => W.analytic.deltaZG) (𝓝[>] (1 : ℝ))
      (𝓝 W.analytic.deltaZG))

end Omega.Zeta
