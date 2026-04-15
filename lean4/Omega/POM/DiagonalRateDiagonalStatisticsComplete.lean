import Mathlib.Tactic

namespace Omega.POM

/-- The diagonal retention statistic recovered from the closed form `p_δ(x) = (1 + κ) / t_x`. -/
def diagonalStatistic {α : Type*} (κ : ℚ) (t : α → ℚ) (x : α) : ℚ :=
  (1 + κ) / t x

/-- A strictly decreasing witness function with unique root at `κ`. -/
def diagonalRootWitness (κ : ℚ) (u : ℚ) : ℚ :=
  κ - u

/-- The background weight recovered from the diagonal denominator. -/
def diagonalBackground {α : Type*} (t : α → ℚ) (x : α) : ℚ :=
  1 / t x

/-- The scalar distortion parameter attached to the diagonal statistic. -/
def diagonalDistortion (κ : ℚ) : ℚ :=
  1 + κ

/-- The stationary law reconstructed from the background weight and the distortion. -/
def diagonalStationary {α : Type*} (κ : ℚ) (t : α → ℚ) (x : α) : ℚ :=
  diagonalDistortion κ * diagonalBackground t x

/-- The full kernel obtained by diagonal recovery together with the off-diagonal refresh factor. -/
def diagonalKernel {α : Type*} [DecidableEq α] (κ δ : ℚ) (t : α → ℚ) (x y : α) : ℚ :=
  if x = y then diagonalStatistic κ t x else δ * diagonalStationary κ t y

/-- Paper-facing completeness package for the diagonal statistics.
    thm:pom-diagonal-rate-diagonal-statistics-complete -/
theorem paper_pom_diagonal_rate_diagonal_statistics_complete
    {α : Type*} [Fintype α] [DecidableEq α] (κ δ : ℚ) (t : α → ℚ) :
    let p := diagonalStatistic κ t
    let F := diagonalRootWitness κ
    let w := diagonalBackground t
    let ξ := diagonalDistortion κ
    let π := diagonalStationary κ t
    let K := diagonalKernel κ δ t
    (∀ x, p x = (1 + κ) / t x) ∧
      StrictAnti F ∧
      F κ = 0 ∧
      (∀ u, F u = 0 → u = κ) ∧
      ξ = 1 + κ ∧
      (∀ x, w x = 1 / t x) ∧
      (∀ x, π x = ξ * w x) ∧
      (∀ x, p x = ξ * w x) ∧
      (∀ x y, K x y = if x = y then p x else δ * π y) := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro a b hab
    dsimp [diagonalRootWitness]
    linarith
  · simp [diagonalRootWitness]
  · intro u hu
    dsimp [diagonalRootWitness] at hu
    linarith
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    simp [diagonalStatistic, diagonalDistortion, diagonalBackground, div_eq_mul_inv]
  · intro x y
    by_cases h : x = y
    · simp [diagonalKernel, h]
    · simp [diagonalKernel, h]

end Omega.POM
