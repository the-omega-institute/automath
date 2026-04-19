import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Discussion.ToeplitzNegativeAtomThreshold

namespace Omega.Discussion

/-- Horizon depth of the off-critical disk image in the fixed Cayley chart. -/
noncomputable def discussionHorizonDepth (γ δ : ℝ) : ℝ :=
  4 * δ / (γ ^ 2 + (1 + δ) ^ 2)

/-- Minimal detectable order, modeled as the inverse horizon depth. -/
noncomputable def discussionMinimalDetectableOrder (γ δ : ℝ) : ℝ :=
  1 / discussionHorizonDepth γ δ

/-- Under bounded off-critical depth `δ` and large height `|γ|`, the explicit horizon-depth
formula is equivalent to the quadratic area law `h(ρ) ~ δ / γ²`, hence
`N_min(ρ) = h(ρ)⁻¹ ~ γ² / δ`.
    cor:discussion-zk-area-law-gamma2-delta -/
theorem paper_discussion_zk_area_law_gamma2_delta
    {γ δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ : 2 ≤ |γ|) :
    discussionMinimalDetectableOrder γ δ = (γ ^ 2 + (1 + δ) ^ 2) / (4 * δ) ∧
      2 * δ / γ ^ 2 ≤ discussionHorizonDepth γ δ ∧
      discussionHorizonDepth γ δ ≤ 4 * δ / γ ^ 2 ∧
      γ ^ 2 / (4 * δ) ≤ discussionMinimalDetectableOrder γ δ ∧
      discussionMinimalDetectableOrder γ δ ≤ γ ^ 2 / (2 * δ) := by
  have hγsq_ge : 4 ≤ γ ^ 2 := by
    nlinarith [sq_abs γ, hγ]
  have hγsq_pos : 0 < γ ^ 2 := by
    linarith
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ0
  have honeδ_sq_le : (1 + δ) ^ 2 ≤ 4 := by
    nlinarith
  have hden_pos : 0 < γ ^ 2 + (1 + δ) ^ 2 := by
    positivity
  have hden_le : γ ^ 2 + (1 + δ) ^ 2 ≤ 2 * γ ^ 2 := by
    nlinarith
  have hdepth_eq :
      discussionMinimalDetectableOrder γ δ = (γ ^ 2 + (1 + δ) ^ 2) / (4 * δ) := by
    unfold discussionMinimalDetectableOrder discussionHorizonDepth
    field_simp [hδ0.ne', hden_pos.ne']
  have hLowerDepth : 2 * δ / γ ^ 2 ≤ discussionHorizonDepth γ δ := by
    unfold discussionHorizonDepth
    rw [div_le_div_iff₀ hγsq_pos hden_pos]
    nlinarith
  have hUpperDepth : discussionHorizonDepth γ δ ≤ 4 * δ / γ ^ 2 := by
    unfold discussionHorizonDepth
    rw [div_le_div_iff₀ hden_pos hγsq_pos]
    nlinarith
  have hLowerOrder : γ ^ 2 / (4 * δ) ≤ discussionMinimalDetectableOrder γ δ := by
    rw [hdepth_eq]
    rw [div_le_div_iff₀ (by positivity : 0 < 4 * δ) (by positivity : 0 < 4 * δ)]
    nlinarith
  have hUpperOrder : discussionMinimalDetectableOrder γ δ ≤ γ ^ 2 / (2 * δ) := by
    rw [hdepth_eq]
    rw [div_le_div_iff₀ (by positivity : 0 < 4 * δ) (by positivity : 0 < 2 * δ)]
    nlinarith
  refine ⟨hdepth_eq, hLowerDepth, hUpperDepth, hLowerOrder, hUpperOrder⟩

end Omega.Discussion
