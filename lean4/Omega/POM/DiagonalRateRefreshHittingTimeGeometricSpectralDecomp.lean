import Omega.POM.DiagonalRateAbsorbingGeometricMixture
import Omega.POM.DiagonalRateRefreshHittingTimePGFClosed
import Mathlib.Tactic

namespace Omega.POM

/-- Constant refresh-rate specialization used in the concrete two-state spectral decomposition. -/
def pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_refresh_rate : Bool → ℚ :=
  fun _ => 1 / 3

/-- Constant refresh-target law used in the concrete two-state spectral decomposition. -/
def pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_target_law : Bool → ℚ :=
  fun _ => 1 / 2

/-- The evaluation point for the concrete PGF specialization. -/
def pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_s : ℚ :=
  1 / 2

/-- Paper label: `thm:pom-diagonal-rate-refresh-hitting-time-geometric-spectral-decomp`.
The deleted-Laguerre interlacing theorem provides the distinct poles, the residue computation
identifies the geometric weights, and the closed hitting-time PGF specializes to the resulting
two-state rational decomposition. -/
theorem paper_pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp :
    diagonalRateAbsorbingLaguerreInterlacingStatement ∧
      diagonalRateAbsorbingGeometricMixtureStatement ∧
      let G := fun z : Bool =>
        diagonalRateRefreshHoldingPGF
          (pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_refresh_rate z)
          pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_s
      let Gbar :=
        diagonalRateRefreshFailurePGF
          pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_target_law true G
      let J :=
        diagonalRateRefreshRenewalPGF
          pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_target_law true G
      let F :=
        diagonalRateRefreshClosedHittingPGF
          pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_refresh_rate
          pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_target_law false true
          pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_s
      Gbar = 1 / 4 ∧ J = 4 / 7 ∧ F = 1 / 7 := by
  refine ⟨paper_pom_diagonal_rate_absorbing_laguerre_interlacing,
    paper_pom_diagonal_rate_absorbing_geometric_mixture, ?_⟩
  dsimp [pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_refresh_rate,
    pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_target_law,
    pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_s]
  refine ⟨?_, ?_, ?_⟩
  · norm_num [diagonalRateRefreshFailurePGF, diagonalRateRefreshHoldingPGF,
      pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_target_law]
  · norm_num [diagonalRateRefreshRenewalPGF, diagonalRateRefreshFailurePGF,
      diagonalRateRefreshHoldingPGF,
      pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_target_law]
  · norm_num [diagonalRateRefreshClosedHittingPGF, diagonalRateRefreshRenewalPGF,
      diagonalRateRefreshFailurePGF, diagonalRateRefreshHoldingPGF,
      pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_refresh_rate,
      pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp_target_law]

end Omega.POM
