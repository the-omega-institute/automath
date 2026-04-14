import Mathlib.Tactic

namespace Omega.Zeta

/-- Visibility function `q(ρ) = (1 − ρ) / (1 + ρ)`.
    prop:xi-golden-radius-delta-visibility-equivalence -/
noncomputable def visibilityQ (ρ : ℝ) : ℝ := (1 - ρ) / (1 + ρ)

/-- Inverse radius: `ρ*(δ) = q(δ) = (1 − δ) / (1 + δ)`.
    prop:xi-golden-radius-delta-visibility-equivalence -/
noncomputable def visibilityRhoStar (δ : ℝ) : ℝ := visibilityQ δ

/-- Self-inverse: `q(ρ*(δ)) = δ`.
    prop:xi-golden-radius-delta-visibility-equivalence -/
theorem visibilityQ_rhoStar (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    visibilityQ (visibilityRhoStar δ) = δ := by
  unfold visibilityRhoStar visibilityQ
  have h1 : (1 + δ) > 0 := by linarith
  have h1ne : (1 + δ) ≠ 0 := ne_of_gt h1
  field_simp
  ring

/-- Strict antitonicity of `q` on `(−1, 1)`.
    prop:xi-golden-radius-delta-visibility-equivalence -/
theorem visibilityQ_strictAntitono (ρ₁ ρ₂ : ℝ)
    (h1 : -1 < ρ₁) (h2 : ρ₁ < ρ₂) (_h3 : ρ₂ < 1) :
    visibilityQ ρ₂ < visibilityQ ρ₁ := by
  unfold visibilityQ
  have hd1 : 0 < 1 + ρ₁ := by linarith
  have hd2 : 0 < 1 + ρ₂ := by linarith
  rw [div_lt_div_iff₀ hd2 hd1]
  nlinarith

/-- `ρ*(δ) ∈ (−1, 1)` when `δ ∈ (0, 1)`.
    prop:xi-golden-radius-delta-visibility-equivalence -/
theorem visibilityRhoStar_mem_open_interval
    (δ : ℝ) (hδ1 : 0 < δ) (hδ2 : δ < 1) :
    -1 < visibilityRhoStar δ ∧ visibilityRhoStar δ < 1 := by
  unfold visibilityRhoStar visibilityQ
  have hpos : 0 < 1 + δ := by linarith
  refine ⟨?_, ?_⟩
  · -- (1 - δ) / (1 + δ) > -1 iff 1 - δ > -(1 + δ), i.e. 1 > -1 after simplify
    rw [lt_div_iff₀ hpos]
    linarith
  · rw [div_lt_one hpos]
    linarith

/-- Main equivalence: `ρ > ρ*(δ) ↔ q(ρ) < δ` on the valid parameter range.
    prop:xi-golden-radius-delta-visibility-equivalence -/
theorem visibility_equivalence (ρ δ : ℝ)
    (hρ1 : -1 < ρ) (hρ2 : ρ < 1) (hδ1 : 0 < δ) (hδ2 : δ < 1) :
    ρ > visibilityRhoStar δ ↔ visibilityQ ρ < δ := by
  obtain ⟨hstar_lb, hstar_ub⟩ := visibilityRhoStar_mem_open_interval δ hδ1 hδ2
  constructor
  · intro hρgt
    have hanti := visibilityQ_strictAntitono (visibilityRhoStar δ) ρ hstar_lb hρgt hρ2
    rw [visibilityQ_rhoStar δ hδ1 hδ2] at hanti
    exact hanti
  · intro hqlt
    by_contra hcontra
    push_neg at hcontra
    -- hcontra : ρ ≤ ρ*(δ)
    rcases lt_or_eq_of_le hcontra with hlt | heq
    · have hanti := visibilityQ_strictAntitono ρ (visibilityRhoStar δ) hρ1 hlt hstar_ub
      rw [visibilityQ_rhoStar δ hδ1 hδ2] at hanti
      linarith
    · rw [heq, visibilityQ_rhoStar δ hδ1 hδ2] at hqlt
      exact absurd hqlt (lt_irrefl δ)

/-- Paper package: golden-radius δ-visibility equivalence.
    prop:xi-golden-radius-delta-visibility-equivalence -/
theorem paper_xi_golden_radius_delta_visibility :
    (∀ δ : ℝ, 0 < δ → δ < 1 → visibilityQ (visibilityRhoStar δ) = δ) ∧
    (∀ ρ₁ ρ₂ : ℝ, -1 < ρ₁ → ρ₁ < ρ₂ → ρ₂ < 1 →
      visibilityQ ρ₂ < visibilityQ ρ₁) ∧
    (∀ ρ δ : ℝ, -1 < ρ → ρ < 1 → 0 < δ → δ < 1 →
      (ρ > visibilityRhoStar δ ↔ visibilityQ ρ < δ)) :=
  ⟨visibilityQ_rhoStar, visibilityQ_strictAntitono, visibility_equivalence⟩

end Omega.Zeta
