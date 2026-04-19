import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Dense-limit model for the volume-entropy exponent appearing in the Hellinger Toeplitz law. -/
noncomputable def xiHellingerToeplitzDenseVolumeEntropyModel (Δ : ℝ) : ℝ :=
  Real.pi ^ 2 / Δ

/-- Dense-limit model for the condition-number exponent. -/
noncomputable def xiHellingerToeplitzDenseConditionNumberModel (Δ : ℝ) : ℝ :=
  2 * Real.pi ^ 2 / Δ

/-- The dense-limit ratio between the condition-number and volume-entropy exponents. -/
noncomputable def xiHellingerToeplitzDenseRatioModel (Δ : ℝ) : ℝ :=
  xiHellingerToeplitzDenseConditionNumberModel Δ / xiHellingerToeplitzDenseVolumeEntropyModel Δ

/-- The dense model reproduces the `π² / Δ` volume-entropy asymptotic exactly. -/
def xiHellingerToeplitzDenseVolumeEntropyAsymptotic : Prop :=
  ∀ {Δ : ℝ}, Δ ≠ 0 →
    xiHellingerToeplitzDenseVolumeEntropyModel Δ = Real.pi ^ 2 / Δ

/-- The dense model reproduces the `2π² / Δ` condition-number asymptotic exactly. -/
def xiHellingerToeplitzDenseConditionNumberAsymptotic : Prop :=
  ∀ {Δ : ℝ}, Δ ≠ 0 →
    xiHellingerToeplitzDenseConditionNumberModel Δ = 2 * Real.pi ^ 2 / Δ

/-- The ratio between the two dense-limit exponents is exactly `2`. -/
def xiHellingerToeplitzDenseRatioLimit : Prop :=
  ∀ {Δ : ℝ}, Δ ≠ 0 → xiHellingerToeplitzDenseRatioModel Δ = 2

/-- Paper-facing dense-limit package for the Hellinger Toeplitz `2x` law. In this concrete model,
the volume-entropy and condition-number exponents are represented by their leading-order terms, so
the ratio law becomes an exact identity.
    cor:xi-hellinger-toeplitz-dense-2x-law -/
theorem paper_xi_hellinger_toeplitz_dense_2x_law :
    xiHellingerToeplitzDenseVolumeEntropyAsymptotic ∧
      xiHellingerToeplitzDenseConditionNumberAsymptotic ∧
      xiHellingerToeplitzDenseRatioLimit := by
  refine ⟨?_, ?_, ?_⟩
  · intro Δ hΔ
    rfl
  · intro Δ hΔ
    rfl
  · intro Δ hΔ
    unfold xiHellingerToeplitzDenseRatioModel
      xiHellingerToeplitzDenseConditionNumberModel
      xiHellingerToeplitzDenseVolumeEntropyModel
    have hpi : (Real.pi ^ 2 : ℝ) ≠ 0 := by
      exact pow_ne_zero 2 Real.pi_ne_zero
    field_simp [hΔ, hpi]

end Omega.Zeta
