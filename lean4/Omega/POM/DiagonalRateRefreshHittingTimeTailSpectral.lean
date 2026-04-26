import Mathlib.Tactic
import Omega.POM.DiagonalRateRefreshHittingTimeGeometricSpectralDecomp

namespace Omega.POM

/-- The spectral tail obtained by summing the two geometric components of the hitting-time law. -/
def pom_diagonal_rate_refresh_hitting_time_tail_spectral_tail (k : ℕ) : ℚ :=
  diagonalRateAbsorbingGeometricWeight₁ * diagonalRateAbsorbingGeometricLambda₁ ^ k +
    diagonalRateAbsorbingGeometricWeight₂ * diagonalRateAbsorbingGeometricLambda₂ ^ k

/-- Concrete statement of the diagonal refresh hitting-time spectral tail law. -/
def pom_diagonal_rate_refresh_hitting_time_tail_spectral_statement : Prop :=
  diagonalRateAbsorbingLaguerreInterlacingStatement ∧
    diagonalRateAbsorbingGeometricMixtureStatement ∧
    (∀ k : ℕ,
      pom_diagonal_rate_refresh_hitting_time_tail_spectral_tail k =
        diagonalRateAbsorbingGeometricWeight₁ * diagonalRateAbsorbingGeometricLambda₁ ^ k +
          diagonalRateAbsorbingGeometricWeight₂ * diagonalRateAbsorbingGeometricLambda₂ ^ k) ∧
    pom_diagonal_rate_refresh_hitting_time_tail_spectral_tail 0 = 1 ∧
    ∀ k : ℕ,
      pom_diagonal_rate_refresh_hitting_time_tail_spectral_tail (k + 1) =
        pom_diagonal_rate_refresh_hitting_time_tail_spectral_tail k -
          diagonalRateAbsorbingGeometricMass (k + 1)

/-- Paper label: `cor:pom-diagonal-rate-refresh-hitting-time-tail-spectral`. -/
theorem paper_pom_diagonal_rate_refresh_hitting_time_tail_spectral :
    pom_diagonal_rate_refresh_hitting_time_tail_spectral_statement := by
  rcases paper_pom_diagonal_rate_refresh_hitting_time_geometric_spectral_decomp with
    ⟨hLag, hGeom, _⟩
  rcases hGeom with ⟨hWeight₁, hWeight₂, hWeight₁_pos, hWeight₂_pos, hWeight_sum,
    hLambda₁, hLambda₂, hMass⟩
  refine
    ⟨hLag, ⟨hWeight₁, hWeight₂, hWeight₁_pos, hWeight₂_pos, hWeight_sum, hLambda₁, hLambda₂,
      hMass⟩, ?_, ?_, ?_⟩
  · intro k
    rfl
  · simpa [pom_diagonal_rate_refresh_hitting_time_tail_spectral_tail] using hWeight_sum
  · intro k
    have hMass' :
        diagonalRateAbsorbingGeometricMass (k + 1) =
          diagonalRateAbsorbingGeometricWeight₁ * (1 - diagonalRateAbsorbingGeometricLambda₁) *
              diagonalRateAbsorbingGeometricLambda₁ ^ k +
            diagonalRateAbsorbingGeometricWeight₂ * (1 - diagonalRateAbsorbingGeometricLambda₂) *
              diagonalRateAbsorbingGeometricLambda₂ ^ k := by
      simpa using hMass (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
    rw [hMass']
    unfold pom_diagonal_rate_refresh_hitting_time_tail_spectral_tail
    ring

end Omega.POM
