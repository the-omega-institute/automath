import Mathlib.Tactic

namespace Omega.POM

/-- The linear factor `Q_κ(z) = 1 - κ z` from the diagonal accept-refresh denominator. -/
def diagonalAcceptRefreshQ (κ z : ℚ) : ℚ :=
  1 - κ * z

/-- The quadratic denominator `P_{κ,δ}(z) = (1 - κ z)(1 - δ z)`. -/
def diagonalAcceptRefreshP (κ δ z : ℚ) : ℚ :=
  1 - (κ + δ) * z + κ * δ * z ^ 2

/-- The closed rational form of the accept-refresh strong-stationary-time PGF. -/
def diagonalAcceptRefreshSSTPGF (κ δ z : ℚ) : ℚ :=
  z / diagonalAcceptRefreshP κ δ z

/-- Rank-one resolvent equation for the diagonal accept-refresh PGF. -/
def diagonalAcceptRefreshRankOneSystem (κ δ z G : ℚ) : Prop :=
  diagonalAcceptRefreshP κ δ z * G = z

/-- The diagonal accept-refresh SST PGF solves the rank-one linear system and its denominator
factors into the two linear pieces `Q_κ` and `Q_δ`, giving the closed rational form.
    thm:pom-diagonal-rate-accept-refresh-sst-pgf -/
theorem paper_pom_diagonal_rate_accept_refresh_sst_pgf
    (κ δ z : ℚ) (hP : diagonalAcceptRefreshP κ δ z ≠ 0) :
    diagonalAcceptRefreshQ κ z * diagonalAcceptRefreshQ δ z = diagonalAcceptRefreshP κ δ z ∧
      diagonalAcceptRefreshRankOneSystem κ δ z (diagonalAcceptRefreshSSTPGF κ δ z) ∧
      diagonalAcceptRefreshSSTPGF κ δ z =
        z / (diagonalAcceptRefreshQ κ z * diagonalAcceptRefreshQ δ z) := by
  refine ⟨by
    unfold diagonalAcceptRefreshQ diagonalAcceptRefreshP
    ring, ?_, ?_⟩
  · unfold diagonalAcceptRefreshRankOneSystem diagonalAcceptRefreshSSTPGF
    field_simp [hP]
  · unfold diagonalAcceptRefreshSSTPGF
    rw [show diagonalAcceptRefreshP κ δ z =
      diagonalAcceptRefreshQ κ z * diagonalAcceptRefreshQ δ z by
        unfold diagonalAcceptRefreshQ diagonalAcceptRefreshP
        ring]

end Omega.POM
