import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Omega.Folding

/-- Closed-form limit proxy used for the identifiable power-divergence scan. -/
noncomputable def foldBinPhiPowerDivergence (α ξ : ℝ) : ℝ :=
  ξ ^ (α - 1)

/-- The closed-form power-divergence proxy is strictly increasing on `(1, ∞)` for every `α > 1`,
so the parameter `ξ` is identifiable from its value.
    prop:fold-bin-phi-identifiable-power-divergence -/
theorem paper_fold_bin_phi_identifiable_power_divergence
    (α ξ₁ ξ₂ : ℝ) (hα : 1 < α) (hξ₁ : 1 < ξ₁) (hξ₂ : ξ₁ < ξ₂) :
    foldBinPhiPowerDivergence α ξ₁ < foldBinPhiPowerDivergence α ξ₂ := by
  have hexp : 0 < α - 1 := sub_pos.mpr hα
  have hmono := Real.strictMonoOn_rpow_Ici_of_exponent_pos hexp
  have hξ₁_mem : ξ₁ ∈ Set.Ici (0 : ℝ) := by
    show 0 ≤ ξ₁
    linarith
  have hξ₂_mem : ξ₂ ∈ Set.Ici (0 : ℝ) := by
    show 0 ≤ ξ₂
    linarith [hξ₁, hξ₂]
  simpa [foldBinPhiPowerDivergence] using hmono hξ₁_mem hξ₂_mem hξ₂

end Omega.Folding
