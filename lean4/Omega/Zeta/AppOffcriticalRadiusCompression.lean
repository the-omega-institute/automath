import Mathlib.Tactic
import Omega.Zeta.CayleyDepthIdentity

namespace Omega.Zeta

open CayleyDepthIdentity

/-- Squared Cayley modulus for the off-critical point `γ + iδ`. -/
noncomputable def appOffcriticalModSq (γ δ : ℝ) : ℝ :=
  cayleyModSq δ γ 0

/-- Boundary depth `1 - |w_ρ|²` for the off-critical Cayley point. -/
noncomputable def appOffcriticalBoundaryDepth (γ δ : ℝ) : ℝ :=
  1 - appOffcriticalModSq γ δ

lemma appOffcriticalModSq_lt_one (γ δ : ℝ) (hδ : 0 < δ) :
    appOffcriticalModSq γ δ < 1 := by
  unfold appOffcriticalModSq cayleyModSq
  have hden_pos : 0 < γ ^ 2 + (1 + δ) ^ 2 := by positivity
  have hnum_lt_den : γ ^ 2 + (1 - δ) ^ 2 < γ ^ 2 + (1 + δ) ^ 2 := by
    nlinarith
  simpa using (div_lt_one hden_pos).2 hnum_lt_den

lemma appOffcriticalModSq_closed_form (γ δ : ℝ) :
    appOffcriticalModSq γ δ =
      (γ ^ 2 + (δ - 1) ^ 2) / (γ ^ 2 + (δ + 1) ^ 2) := by
  unfold appOffcriticalModSq cayleyModSq
  ring_nf

lemma appOffcriticalBoundaryDepth_closed_form (γ δ : ℝ) (hδ : 0 < δ) :
    appOffcriticalBoundaryDepth γ δ = 4 * δ / (γ ^ 2 + (δ + 1) ^ 2) := by
  unfold appOffcriticalBoundaryDepth appOffcriticalModSq cayleyModSq
  have hden_ne : γ ^ 2 + (1 + δ) ^ 2 ≠ 0 := by
    have hden_pos : 0 < γ ^ 2 + (1 + δ) ^ 2 := by positivity
    exact ne_of_gt hden_pos
  field_simp [hden_ne]
  ring_nf

/-- Paper-facing off-critical Cayley compression package: the point is strictly inside the unit
disk, and both `|w_ρ|²` and `1 - |w_ρ|²` admit the stated closed forms.
    prop:app-offcritical-radius-compression -/
theorem paper_app_offcritical_radius_compression :
    (∀ γ δ : ℝ, 0 < δ → appOffcriticalModSq γ δ < 1) ∧
      (∀ γ δ : ℝ,
        appOffcriticalModSq γ δ =
          (γ ^ 2 + (δ - 1) ^ 2) / (γ ^ 2 + (δ + 1) ^ 2)) ∧
      (∀ γ δ : ℝ, 0 < δ →
        appOffcriticalBoundaryDepth γ δ = 4 * δ / (γ ^ 2 + (δ + 1) ^ 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro γ δ hδ
    exact appOffcriticalModSq_lt_one γ δ hδ
  · intro γ δ
    exact appOffcriticalModSq_closed_form γ δ
  · intro γ δ hδ
    exact appOffcriticalBoundaryDepth_closed_form γ δ hδ

end Omega.Zeta
