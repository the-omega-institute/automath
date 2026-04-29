import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-hellinger-gram-cluster-additivity-exp`. -/
theorem paper_xi_hellinger_gram_cluster_additivity_exp {κ₁ κ₂ : ℕ}
    {L K Cnorm logDetDefect : ℝ} (hK : 0 ≤ K)
    (hSchur : |logDetDefect| ≤ K * Cnorm ^ 2)
    (hC : Cnorm ^ 2 ≤ (κ₁ : ℝ) * (κ₂ : ℝ) * L ^ 2 * Real.exp (-L)) :
    |logDetDefect| ≤ K * (κ₁ : ℝ) * (κ₂ : ℝ) * L ^ 2 * Real.exp (-L) := by
  calc
    |logDetDefect| ≤ K * Cnorm ^ 2 := hSchur
    _ ≤ K * ((κ₁ : ℝ) * (κ₂ : ℝ) * L ^ 2 * Real.exp (-L)) :=
      mul_le_mul_of_nonneg_left hC hK
    _ = K * (κ₁ : ℝ) * (κ₂ : ℝ) * L ^ 2 * Real.exp (-L) := by ring

end Omega.Zeta
