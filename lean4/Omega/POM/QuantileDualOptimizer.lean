import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-quantile-dual-optimizer`.
Concrete dual optimizer data for an integer-quantile Chernoff family. -/
structure pom_quantile_dual_optimizer_data where
  candidateExponent : ℝ
  dualFunctional : ℝ
  chernoffExponent : ℕ → ℝ
  chernoff_certificate :
    ∀ q : ℕ, 2 ≤ q → candidateExponent ≤ chernoffExponent q
  dual_upper_bound :
    ∀ x : ℝ, (∀ q : ℕ, 2 ≤ q → x ≤ chernoffExponent q) → x ≤ dualFunctional
  dual_le_candidate : dualFunctional ≤ candidateExponent

namespace pom_quantile_dual_optimizer_data

/-- The supplied candidate is exactly the optimizing dual exponent, and it satisfies every
integer Chernoff certificate for `q >= 2`. -/
def statement (D : pom_quantile_dual_optimizer_data) : Prop :=
  D.dualFunctional = D.candidateExponent ∧
    ∀ q : ℕ, 2 ≤ q → D.candidateExponent ≤ D.chernoffExponent q

end pom_quantile_dual_optimizer_data

/-- Paper label: `cor:pom-quantile-dual-optimizer`. -/
theorem paper_pom_quantile_dual_optimizer
    (D : pom_quantile_dual_optimizer_data) : D.statement := by
  refine ⟨?_, D.chernoff_certificate⟩
  exact le_antisymm D.dual_le_candidate
    (D.dual_upper_bound D.candidateExponent D.chernoff_certificate)

end Omega.POM
