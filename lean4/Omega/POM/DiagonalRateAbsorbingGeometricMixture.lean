import Omega.POM.DiagonalRateAbsorbingHitPGF
import Omega.POM.DiagonalRateAbsorbingLaguerreInterlacing
import Mathlib.Tactic

namespace Omega.POM

/-- The two deleted-point secular roots from the concrete Laguerre toy model. -/
def diagonalRateAbsorbingGeometricRoot₁ : ℚ := 2

/-- The larger deleted-point secular root from the concrete Laguerre toy model. -/
def diagonalRateAbsorbingGeometricRoot₂ : ℚ := 20 / 3

/-- The corresponding geometric contraction factor `κ / z₁` with `κ = 1`. -/
def diagonalRateAbsorbingGeometricLambda₁ : ℚ := 1 / diagonalRateAbsorbingGeometricRoot₁

/-- The second geometric contraction factor `κ / z₂` with `κ = 1`. -/
def diagonalRateAbsorbingGeometricLambda₂ : ℚ := 1 / diagonalRateAbsorbingGeometricRoot₂

/-- The numerator entering the residue formula. -/
def diagonalRateAbsorbingGeometricNumerator (z : ℚ) : ℚ := 5 - z

/-- The deleted-point Laguerre denominator with roots `2` and `20 / 3`. -/
def diagonalRateAbsorbingGeometricDenominator (z : ℚ) : ℚ := (z - 2) * (3 * z - 20)

/-- The derivative of the deleted-point Laguerre denominator. -/
def diagonalRateAbsorbingGeometricDenominatorDerivative (z : ℚ) : ℚ := 6 * z - 26

/-- The common residue prefactor `-κ (t_x - κ) / (t_y - κ)` in the concrete toy model with
`κ = 1`, `t_x = 18`, and `t_y = 5`. -/
def diagonalRateAbsorbingGeometricResidueScale : ℚ :=
  -((1 : ℚ) * ((18 : ℚ) - 1) / ((5 : ℚ) - 1))

/-- The residue weight attached to a secular root `z`. -/
def diagonalRateAbsorbingGeometricResidueWeight (z : ℚ) : ℚ :=
  diagonalRateAbsorbingGeometricResidueScale * diagonalRateAbsorbingGeometricNumerator z /
    ((z - 1) * diagonalRateAbsorbingGeometricDenominatorDerivative z)

/-- The first mixture coefficient extracted from the residue at `z = 2`. -/
def diagonalRateAbsorbingGeometricWeight₁ : ℚ :=
  diagonalRateAbsorbingGeometricResidueWeight diagonalRateAbsorbingGeometricRoot₁

/-- The second mixture coefficient extracted from the residue at `z = 20 / 3`. -/
def diagonalRateAbsorbingGeometricWeight₂ : ℚ :=
  diagonalRateAbsorbingGeometricResidueWeight diagonalRateAbsorbingGeometricRoot₂

/-- The concrete absorbing hitting distribution written as a two-point geometric mixture. -/
def diagonalRateAbsorbingGeometricMass (k : ℕ) : ℚ :=
  if 1 ≤ k then
    diagonalRateAbsorbingGeometricWeight₁ * (1 - diagonalRateAbsorbingGeometricLambda₁) *
        diagonalRateAbsorbingGeometricLambda₁ ^ (k - 1) +
      diagonalRateAbsorbingGeometricWeight₂ * (1 - diagonalRateAbsorbingGeometricLambda₂) *
        diagonalRateAbsorbingGeometricLambda₂ ^ (k - 1)
  else
    0

/-- Concrete paper-facing package for the absorbing geometric-mixture statement. -/
def diagonalRateAbsorbingGeometricMixtureStatement : Prop :=
  diagonalRateAbsorbingGeometricWeight₁ = 51 / 56 ∧
    diagonalRateAbsorbingGeometricWeight₂ = 5 / 56 ∧
    0 < diagonalRateAbsorbingGeometricWeight₁ ∧
    0 < diagonalRateAbsorbingGeometricWeight₂ ∧
    diagonalRateAbsorbingGeometricWeight₁ + diagonalRateAbsorbingGeometricWeight₂ = 1 ∧
    diagonalRateAbsorbingGeometricLambda₁ = 1 / diagonalRateAbsorbingGeometricRoot₁ ∧
    diagonalRateAbsorbingGeometricLambda₂ = 1 / diagonalRateAbsorbingGeometricRoot₂ ∧
    ∀ k : ℕ,
      1 ≤ k →
        diagonalRateAbsorbingGeometricMass k =
          diagonalRateAbsorbingGeometricWeight₁ * (1 - diagonalRateAbsorbingGeometricLambda₁) *
              diagonalRateAbsorbingGeometricLambda₁ ^ (k - 1) +
            diagonalRateAbsorbingGeometricWeight₂ *
              (1 - diagonalRateAbsorbingGeometricLambda₂) *
              diagonalRateAbsorbingGeometricLambda₂ ^ (k - 1)

/-- Paper label: `thm:pom-diagonal-rate-absorbing-geometric-mixture`.
In the concrete two-root Laguerre toy model, the residue weights are positive, sum to `1`, and
the hitting law is exactly a convex combination of two geometric laws with parameters
`λ₁ = 1 / 2` and `λ₂ = 3 / 20`. -/
theorem paper_pom_diagonal_rate_absorbing_geometric_mixture :
    diagonalRateAbsorbingGeometricMixtureStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [diagonalRateAbsorbingGeometricWeight₁, diagonalRateAbsorbingGeometricResidueWeight,
      diagonalRateAbsorbingGeometricResidueScale, diagonalRateAbsorbingGeometricNumerator,
      diagonalRateAbsorbingGeometricRoot₁, diagonalRateAbsorbingGeometricDenominatorDerivative]
  · norm_num [diagonalRateAbsorbingGeometricWeight₂, diagonalRateAbsorbingGeometricResidueWeight,
      diagonalRateAbsorbingGeometricResidueScale, diagonalRateAbsorbingGeometricNumerator,
      diagonalRateAbsorbingGeometricRoot₂, diagonalRateAbsorbingGeometricDenominatorDerivative]
  · norm_num [diagonalRateAbsorbingGeometricWeight₁, diagonalRateAbsorbingGeometricResidueWeight,
      diagonalRateAbsorbingGeometricResidueScale, diagonalRateAbsorbingGeometricNumerator,
      diagonalRateAbsorbingGeometricRoot₁, diagonalRateAbsorbingGeometricDenominatorDerivative]
  · norm_num [diagonalRateAbsorbingGeometricWeight₂, diagonalRateAbsorbingGeometricResidueWeight,
      diagonalRateAbsorbingGeometricResidueScale, diagonalRateAbsorbingGeometricNumerator,
      diagonalRateAbsorbingGeometricRoot₂, diagonalRateAbsorbingGeometricDenominatorDerivative]
  · norm_num [diagonalRateAbsorbingGeometricWeight₁, diagonalRateAbsorbingGeometricWeight₂,
      diagonalRateAbsorbingGeometricResidueWeight, diagonalRateAbsorbingGeometricResidueScale,
      diagonalRateAbsorbingGeometricNumerator, diagonalRateAbsorbingGeometricRoot₁,
      diagonalRateAbsorbingGeometricRoot₂, diagonalRateAbsorbingGeometricDenominatorDerivative]
  · rfl
  · rfl
  · intro k hk
    simp [diagonalRateAbsorbingGeometricMass, hk]

end Omega.POM
