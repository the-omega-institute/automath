import Mathlib.Tactic
import Omega.Zeta.XiHellingerToeplitzDense2xLaw

namespace Omega.Zeta

/-- The dense-limit stable-inversion bit budget, measured in base-2 digits. -/
noncomputable def xiHellingerToeplitzBitBudgetModel (Δ : ℝ) : ℝ :=
  xiHellingerToeplitzDenseConditionNumberModel Δ / Real.log 2

/-- Paper label: `cor:xi-hellinger-toeplitz-bit-budget-linear-law`. Dividing the dense
condition-number exponent by `log 2` converts the stability threshold to base-2 bits, and the
preceding dense `2x` law turns this into the exact linear relation with the volume-entropy model. -/
theorem paper_xi_hellinger_toeplitz_bit_budget_linear_law {Δ : ℝ} (hΔ : Δ ≠ 0) :
    xiHellingerToeplitzBitBudgetModel Δ =
      (2 / Real.log 2) * xiHellingerToeplitzDenseVolumeEntropyModel Δ := by
  rcases paper_xi_hellinger_toeplitz_dense_2x_law with ⟨hVol, hCond, _⟩
  unfold xiHellingerToeplitzBitBudgetModel
  rw [hCond hΔ, hVol hΔ]
  ring

end Omega.Zeta
