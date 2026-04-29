import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-power-sum-hankel-psd`. -/
theorem paper_pom_power_sum_hankel_psd {α : Type*} [Fintype α] (d : α → ℝ) (r : ℕ) :
    ∀ c : Fin (r + 1) → ℝ, 0 ≤ ∑ x : α, (∑ i : Fin (r + 1), c i * d x ^ (i : ℕ)) ^ 2 := by
  intro c
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

end Omega.POM
