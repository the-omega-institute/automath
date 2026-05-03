import Mathlib.Tactic
import Omega.Zeta.XiHorizonPoleResidueDepthStrength

namespace Omega.Zeta

/-- Bounded positive off-critical displacement used in the redshift package. -/
def xi_horizon_residue_redshift_bounded_delta (δ Δ : ℝ) : Prop :=
  0 < δ ∧ δ ≤ Δ

/-- High-height hypothesis away from the horizontal origin. -/
def xi_horizon_residue_redshift_high_height (γ : ℝ) : Prop :=
  0 < γ ^ 2

/-- The exact horizon-depth closed form. -/
def xi_horizon_residue_redshift_depth_formula (δ γ h : ℝ) : Prop :=
  h = 4 * δ / (γ ^ 2 + (1 + δ) ^ 2)

/-- The exact pole-residue strength closed form. -/
def xi_horizon_residue_redshift_residue_formula (m : ℕ) (δ γ resNorm : ℝ) : Prop :=
  resNorm = 2 * (m : ℝ) / (γ ^ 2 + (1 + δ) ^ 2)

/-- Concrete redshift package: the residue has the same depth scale as the existing
depth-strength law, and both depth and residue are bounded by the high-height denominator. -/
def xi_horizon_residue_redshift_statement : Prop :=
  ∀ (m : ℕ) (δ Δ γ h resNorm : ℝ),
    xi_horizon_residue_redshift_bounded_delta δ Δ →
      xi_horizon_residue_redshift_high_height γ →
        xi_horizon_residue_redshift_depth_formula δ γ h →
          xi_horizon_residue_redshift_residue_formula m δ γ resNorm →
            resNorm = ((m : ℝ) / (2 * δ)) * h ∧
              h ≤ 4 * Δ / γ ^ 2 ∧
                resNorm ≤ 2 * (m : ℝ) / γ ^ 2

/-- Paper label: `cor:xi-horizon-residue-redshift`. -/
theorem paper_xi_horizon_residue_redshift : xi_horizon_residue_redshift_statement := by
  intro m δ Δ γ h resNorm hδΔ hγ hdepth hres
  rcases hδΔ with ⟨hδ, hδ_le⟩
  have hscale :
      resNorm = ((m : ℝ) / (2 * δ)) * h := by
    exact paper_xi_horizon_pole_residue_depth_strength m δ γ h resNorm hδ hdepth hres
  have hden_ge_gamma : γ ^ 2 ≤ γ ^ 2 + (1 + δ) ^ 2 := by
    nlinarith [sq_nonneg (1 + δ)]
  have hdepth_gamma :
      h ≤ 4 * δ / γ ^ 2 := by
    rw [hdepth]
    exact div_le_div_of_nonneg_left (by nlinarith : 0 ≤ 4 * δ) hγ hden_ge_gamma
  have hdelta_bound :
      4 * δ / γ ^ 2 ≤ 4 * Δ / γ ^ 2 := by
    exact div_le_div_of_nonneg_right (by nlinarith : 4 * δ ≤ 4 * Δ) hγ.le
  have hres_gamma :
      resNorm ≤ 2 * (m : ℝ) / γ ^ 2 := by
    rw [hres]
    exact div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * (m : ℝ)) hγ hden_ge_gamma
  exact ⟨hscale, hdepth_gamma.trans hdelta_bound, hres_gamma⟩

end Omega.Zeta
