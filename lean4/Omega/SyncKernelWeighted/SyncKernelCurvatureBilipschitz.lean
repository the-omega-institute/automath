import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Audited statement for the curvature-to-bilipschitz and strong-convexity transfer. -/
def SyncKernelCurvatureBilipschitzStatement
    (α I : ℝ → ℝ) (m M : ℝ) : Prop :=
  (∀ θ₁ θ₂ : ℝ,
      m * |θ₁ - θ₂| ≤ |α θ₁ - α θ₂| ∧ |α θ₁ - α θ₂| ≤ M * |θ₁ - θ₂|) ∧
    ∀ θ : ℝ, 1 / M ≤ deriv (deriv I) (α θ) ∧ deriv (deriv I) (α θ) ≤ 1 / m

/-- Paper label: `prop:sync-kernel-curvature-bilipschitz`. Uniform bounds
`0 < m ≤ α'(θ) ≤ M`, with `α = P'`, give two-sided Lipschitz control of the slope map; the
Legendre identity `I''(α(θ)) = 1 / α'(θ)` then yields the strong-convexity interval. -/
theorem paper_sync_kernel_curvature_bilipschitz
    (α I curvature : ℝ → ℝ) (m M : ℝ)
    (hm : 0 < m) (hM : m ≤ M)
    (hα : ∀ θ : ℝ, HasDerivAt α (curvature θ) θ)
    (hcurv : ∀ θ : ℝ, m ≤ curvature θ ∧ curvature θ ≤ M)
    (hLegendre : ∀ θ : ℝ, deriv (deriv I) (α θ) = 1 / curvature θ) :
    SyncKernelCurvatureBilipschitzStatement α I m M := by
  have hαdiff : Differentiable ℝ α := fun θ => (hα θ).differentiableAt
  have hcurv_lower : ∀ θ : ℝ, m ≤ deriv α θ := by
    intro θ
    simpa [show deriv α θ = curvature θ by exact (hα θ).deriv] using (hcurv θ).1
  have hcurv_upper : ∀ θ : ℝ, deriv α θ ≤ M := by
    intro θ
    simpa [show deriv α θ = curvature θ by exact (hα θ).deriv] using (hcurv θ).2
  have hMpos : 0 < M := lt_of_lt_of_le hm hM
  refine ⟨?_, ?_⟩
  · intro θ₁ θ₂
    rcases le_total θ₁ θ₂ with hθ | hθ
    · have hlower := mul_sub_le_image_sub_of_le_deriv hαdiff hcurv_lower hθ
      have hupper := image_sub_le_mul_sub_of_deriv_le hαdiff hcurv_upper hθ
      have hαnonneg : 0 ≤ α θ₂ - α θ₁ := by
        nlinarith [hlower]
      constructor
      · rw [abs_of_nonpos (sub_nonpos.mpr hθ), abs_of_nonpos (by linarith), neg_sub, neg_sub]
        simpa [sub_eq_add_neg] using hlower
      · rw [abs_of_nonpos (sub_nonpos.mpr hθ), abs_of_nonpos (by linarith), neg_sub, neg_sub]
        simpa [sub_eq_add_neg] using hupper
    · have hlower := mul_sub_le_image_sub_of_le_deriv hαdiff hcurv_lower hθ
      have hupper := image_sub_le_mul_sub_of_deriv_le hαdiff hcurv_upper hθ
      have hαnonneg : 0 ≤ α θ₁ - α θ₂ := by
        nlinarith [hlower]
      constructor
      · rw [abs_of_nonneg (sub_nonneg.mpr hθ), abs_of_nonneg hαnonneg]
        simpa [sub_eq_add_neg]
          using hlower
      · rw [abs_of_nonneg (sub_nonneg.mpr hθ), abs_of_nonneg hαnonneg]
        simpa [sub_eq_add_neg]
          using hupper
  · intro θ
    have hθcurv_pos : 0 < curvature θ := lt_of_lt_of_le hm (hcurv θ).1
    constructor
    · rw [hLegendre θ]
      exact one_div_le_one_div_of_le hθcurv_pos (hcurv θ).2
    · rw [hLegendre θ]
      exact one_div_le_one_div_of_le hm (hcurv θ).1

end

end Omega.SyncKernelWeighted
