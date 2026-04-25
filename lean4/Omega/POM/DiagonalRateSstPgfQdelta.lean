import Omega.POM.DiagonalRateAcceptRefreshSSTPGF
import Omega.POM.DiagonalRateRefreshAcceptStrongStationaryTime
import Omega.POM.DiagonalRateResolventEntryClosedForm

namespace Omega.POM

open DiagonalRateResolventEntryClosedFormData

/-- Paper-facing package bundling the diagonal accept-refresh SST PGF identity, the strong
stationary-time wrapper, and the concrete `Q_δ` resolvent normalization. -/
def pom_diagonal_rate_sst_pgf_qdelta_statement : Prop :=
  (∀ κ δ z : ℚ, diagonalAcceptRefreshP κ δ z ≠ 0 →
      diagonalAcceptRefreshQ κ z * diagonalAcceptRefreshQ δ z = diagonalAcceptRefreshP κ δ z ∧
        diagonalAcceptRefreshRankOneSystem κ δ z (diagonalAcceptRefreshSSTPGF κ δ z) ∧
        diagonalAcceptRefreshSSTPGF κ δ z =
          z / (diagonalAcceptRefreshQ κ z * diagonalAcceptRefreshQ δ z)) ∧
    (∀ D : DiagonalRateAcceptRefreshSSTStrongData,
      D.strongStationaryTime ∧ D.stationaryLawAtStop ∧ D.stopLawIndependent) ∧
    (∀ D : DiagonalRateResolventEntryClosedFormData, ∀ z : ℝ,
      pom_diagonal_rate_resolvent_entry_closed_form_Qdelta D z =
        D.κ * pom_diagonal_rate_resolvent_entry_closed_form_Pdelta D z)

/-- Paper label: `thm:pom-diagonal-rate-sst-pgf-Qdelta`. -/
theorem paper_pom_diagonal_rate_sst_pgf_qdelta :
    pom_diagonal_rate_sst_pgf_qdelta_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro κ δ z hP
    exact paper_pom_diagonal_rate_accept_refresh_sst_pgf κ δ z hP
  · intro D
    exact paper_pom_diagonal_rate_refresh_accept_strong_stationary_time D
  · intro D z
    rfl

end Omega.POM
