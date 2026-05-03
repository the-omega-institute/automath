import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-oracle-rate-budget-bregman-isodistance`. -/
theorem paper_pom_oracle_rate_budget_bregman_isodistance {Q : Type*}
    (inHeat : Q → Prop) (B : Q → ℝ) (a : Q → ℝ) (R : ℝ → ℝ) (r : ℝ)
    (huniq : ∃! q, inHeat q ∧ B q = r)
    (hcost : ∀ q, inHeat q → R (a q) = B q) :
    ∃! q, inHeat q ∧ B q = r ∧ R (a q) = r := by
  rcases huniq with ⟨q, hq, huniq_q⟩
  refine ⟨q, ?_, ?_⟩
  · rcases hq with ⟨hheat, hB⟩
    exact ⟨hheat, hB, by rw [hcost q hheat, hB]⟩
  · intro y hy
    exact huniq_q y ⟨hy.1, hy.2.1⟩

end Omega.POM
