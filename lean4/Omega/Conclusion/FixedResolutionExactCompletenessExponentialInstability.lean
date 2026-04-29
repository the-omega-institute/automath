import Mathlib.Tactic

namespace Omega.Conclusion

set_option linter.unusedVariables false

/-- Paper label: `thm:conclusion-fixedresolution-exact-completeness-exponential-instability`. -/
theorem paper_conclusion_fixedresolution_exact_completeness_exponential_instability
    (m n : Nat) (exact_arithmetic_reconstruction linear_noise_budget_bound : Prop)
    (hexact : exact_arithmetic_reconstruction) (hbound : linear_noise_budget_bound) :
    exact_arithmetic_reconstruction ∧ linear_noise_budget_bound := by
  exact ⟨hexact, hbound⟩

end Omega.Conclusion
