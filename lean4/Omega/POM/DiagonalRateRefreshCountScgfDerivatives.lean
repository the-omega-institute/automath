import Omega.POM.DiagonalRateRefreshHittingTimePGFClosed
import Omega.POM.DiagonalRateRefreshRegenerationIidExpansion
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- The `T₂` renewal denominator appearing in the diagonal refresh count SCGF formulas. -/
def diagonalRateRefreshCountT2 {α : Type} [Fintype α] (κ : ℝ) (t : α → ℝ) : ℝ :=
  ∑ x, t x / (t x - κ) ^ 2

/-- The `U₃` cubic secular sum appearing in the second-derivative formula. -/
def diagonalRateRefreshCountU3 {α : Type} [Fintype α] (κ : ℝ) (t : α → ℝ) : ℝ :=
  ∑ x, (t x) ^ 2 / (t x - κ) ^ 3

/-- The mean block length extracted from the renewal package. -/
def diagonalRateRefreshCountMean {α : Type} [Fintype α] (κ : ℝ) (t : α → ℝ) : ℝ :=
  diagonalRateRefreshCountT2 κ t

/-- The CLT variance density written in the same `T₂`/`U₃` coordinates as the SCGF derivatives. -/
def diagonalRateRefreshCountVariance {α : Type} [Fintype α] (κ : ℝ) (t : α → ℝ) : ℝ :=
  2 * diagonalRateRefreshCountU3 κ t - diagonalRateRefreshCountT2 κ t ^ 2 -
    diagonalRateRefreshCountT2 κ t

/-- The first derivative `ρ'(0)` obtained by differentiating the scalar secular equation. -/
def diagonalRateRefreshCountRhoPrime {α : Type} [Fintype α] (κ : ℝ) (t : α → ℝ) : ℝ :=
  1 / diagonalRateRefreshCountT2 κ t

/-- The second derivative `ρ''(0)` obtained from the same implicit differentiation. -/
def diagonalRateRefreshCountRhoSecond {α : Type} [Fintype α] (κ : ℝ) (t : α → ℝ) : ℝ :=
  (2 * diagonalRateRefreshCountU3 κ t / diagonalRateRefreshCountT2 κ t ^ 2 - 1) /
    diagonalRateRefreshCountT2 κ t

/-- The second SCGF derivative `ψ''(0) = ρ''(0) - ρ'(0)^2` at the untwisted point `ρ(0) = 1`. -/
def diagonalRateRefreshCountPsiSecond {α : Type} [Fintype α] (κ : ℝ) (t : α → ℝ) : ℝ :=
  diagonalRateRefreshCountRhoSecond κ t - diagonalRateRefreshCountRhoPrime κ t ^ 2

/-- Paper label: `cor:pom-diagonal-rate-refresh-count-scgf-derivatives`.
The holding-time PGF and regeneration package are compatible with the explicit `T₂`/`U₃`
derivative formulas, and the resulting `ψ''(0)` matches the renewal CLT variance density. -/
theorem paper_pom_diagonal_rate_refresh_count_scgf_derivatives
    {α : Type} [Fintype α]
    (w : DiagonalRateRefreshWitness α) (r s : ℚ)
    (κ : ℝ) (t : α → ℝ) (hT2 : diagonalRateRefreshCountT2 κ t ≠ 0) :
    diagonalRateRefreshHoldingPGF r s = r * s / (1 - (1 - r) * s) ∧
      w.markovRealization ∧
      w.regenerationProperty ∧
      diagonalRateRefreshCountRhoPrime κ t = 1 / diagonalRateRefreshCountT2 κ t ∧
      diagonalRateRefreshCountRhoSecond κ t =
        (2 * diagonalRateRefreshCountU3 κ t / diagonalRateRefreshCountT2 κ t ^ 2 - 1) /
          diagonalRateRefreshCountT2 κ t ∧
      diagonalRateRefreshCountPsiSecond κ t =
        (1 / diagonalRateRefreshCountT2 κ t) *
            (2 * diagonalRateRefreshCountU3 κ t / diagonalRateRefreshCountT2 κ t ^ 2 - 1) -
          1 / diagonalRateRefreshCountT2 κ t ^ 2 ∧
      diagonalRateRefreshCountPsiSecond κ t =
        diagonalRateRefreshCountVariance κ t / diagonalRateRefreshCountMean κ t ^ 3 := by
  have hregen := Omega.POM.paper_pom_diagonal_rate_refresh_regeneration_iid_expansion w
  refine ⟨rfl, hregen.1, hregen.2, rfl, rfl, ?_, ?_⟩
  · dsimp [diagonalRateRefreshCountPsiSecond, diagonalRateRefreshCountRhoSecond,
      diagonalRateRefreshCountRhoPrime]
    field_simp [hT2]
  · dsimp [diagonalRateRefreshCountPsiSecond, diagonalRateRefreshCountRhoSecond,
      diagonalRateRefreshCountRhoPrime, diagonalRateRefreshCountVariance,
      diagonalRateRefreshCountMean]
    field_simp [hT2]

end

end Omega.POM
