import Mathlib.Tactic

namespace Omega.Zeta.CayleyDepthIdentity

open Real

/-- Cayley depth function `h_{x_0}(ρ) = 4δ / ((γ-x₀)² + (1+δ)²)`.
    con:xi-jensen-soft-threshold-defect-kernel-explicit-sum -/
noncomputable def cayleyDepth (δ γ x₀ : ℝ) : ℝ :=
  4 * δ / ((γ - x₀)^2 + (1 + δ)^2)

/-- Squared modulus of the Cayley map.
    con:xi-jensen-soft-threshold-defect-kernel-explicit-sum -/
noncomputable def cayleyModSq (δ γ x₀ : ℝ) : ℝ :=
  ((γ - x₀)^2 + (1 - δ)^2) / ((γ - x₀)^2 + (1 + δ)^2)

/-- Denominator of the Cayley map is positive when `δ > 0`.
    con:xi-jensen-soft-threshold-defect-kernel-explicit-sum -/
theorem cayley_denom_pos (δ γ x₀ : ℝ) (hδ : 0 < δ) :
    0 < (γ - x₀)^2 + (1 + δ)^2 := by
  have h1 : 0 ≤ (γ - x₀)^2 := sq_nonneg _
  have h2 : 0 < (1 + δ)^2 := by positivity
  linarith

/-- Core identity: `1 - |w|² = h(ρ)`.
    con:xi-jensen-soft-threshold-defect-kernel-explicit-sum -/
theorem one_sub_cayleyModSq_eq_cayleyDepth (δ γ x₀ : ℝ) (hδ : 0 < δ) :
    1 - cayleyModSq δ γ x₀ = cayleyDepth δ γ x₀ := by
  unfold cayleyModSq cayleyDepth
  have hne : ((γ - x₀)^2 + (1 + δ)^2) ≠ 0 := ne_of_gt (cayley_denom_pos δ γ x₀ hδ)
  field_simp
  ring

/-- Restated form: `|w|² = 1 - h(ρ)`.
    con:xi-jensen-soft-threshold-defect-kernel-explicit-sum -/
theorem cayleyModSq_eq_one_sub_cayleyDepth (δ γ x₀ : ℝ) (hδ : 0 < δ) :
    cayleyModSq δ γ x₀ = 1 - cayleyDepth δ γ x₀ := by
  have h := one_sub_cayleyModSq_eq_cayleyDepth δ γ x₀ hδ
  linarith

/-- Positive-part substitution: `max(ρ² - |w|², 0) = max(h(ρ) - (1 - ρ²), 0)`.
    con:xi-jensen-soft-threshold-defect-kernel-explicit-sum -/
theorem positivePart_substitution (ϱ δ γ x₀ : ℝ) (hδ : 0 < δ) :
    max (ϱ^2 - cayleyModSq δ γ x₀) 0 =
      max (cayleyDepth δ γ x₀ - (1 - ϱ^2)) 0 := by
  congr 1
  rw [cayleyModSq_eq_one_sub_cayleyDepth δ γ x₀ hδ]
  ring

/-- Nonnegativity of the Cayley depth.
    con:xi-jensen-soft-threshold-defect-kernel-explicit-sum -/
theorem cayleyDepth_nonneg (δ γ x₀ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ cayleyDepth δ γ x₀ := by
  unfold cayleyDepth
  have h1 : 0 ≤ 4 * δ := by linarith
  have h2 : 0 ≤ (γ - x₀)^2 + (1 + δ)^2 := by positivity
  exact div_nonneg h1 h2

/-- Paper package: ξ Jensen soft-threshold defect kernel — Cayley substitution.
    con:xi-jensen-soft-threshold-defect-kernel-explicit-sum -/
theorem paper_xi_jensen_soft_threshold_defect_kernel_cayley_substitution
    (ϱ δ γ x₀ : ℝ) (hδ : 0 < δ) :
    max (ϱ^2 - cayleyModSq δ γ x₀) 0 =
      max (cayleyDepth δ γ x₀ - (1 - ϱ^2)) 0 :=
  positivePart_substitution ϱ δ γ x₀ hδ

end Omega.Zeta.CayleyDepthIdentity
