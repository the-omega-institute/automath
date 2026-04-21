import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-bulk-curvature-logistic-kernel-decomposition`. -/
theorem paper_xi_bulk_curvature_logistic_kernel_decomposition (κ : ℕ) (hκ : 1 ≤ κ)
    (δ σ : Fin κ → ℝ) (Kbulk : ℝ → ℝ) (hδ : ∀ j, δ j = Real.exp (-σ j))
    (hK : ∀ s : ℝ,
      Kbulk s = (2 * κ - 1 : ℝ) * ∑ j : Fin κ, (Real.exp s * δ j) / (1 + Real.exp s * δ j) ^ 2) :
    ∀ s : ℝ,
      Kbulk s / (2 * κ - 1 : ℝ) =
        ∑ j : Fin κ, Real.exp (s - σ j) / (1 + Real.exp (s - σ j)) ^ 2 := by
  have hkreal : (1 : ℝ) ≤ (κ : ℝ) := by
    exact_mod_cast hκ
  have hscale_pos : (0 : ℝ) < (2 * κ - 1 : ℝ) := by
    nlinarith
  have hscale : (2 * κ - 1 : ℝ) ≠ 0 := by
    linarith
  intro s
  rw [hK s, mul_div_cancel_left₀ _ hscale]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [hδ j]
  have hexp : Real.exp s * Real.exp (-σ j) = Real.exp (s - σ j) := by
    simpa [sub_eq_add_neg] using (Real.exp_add s (-σ j)).symm
  simp [hexp]

end Omega.Zeta
