import Mathlib.Tactic
import Omega.Core.CoprimeSMul

namespace Omega.POM

/-- Paper label: `thm:pom-anom-all-moments-collapse-to-two`. -/
theorem paper_pom_anom_all_moments_collapse_to_two (anom : ℤ) :
    (∀ q : ℤ, 2 ≤ q → q • anom = 0) ↔
      ∃ q₁ q₂ : ℤ,
        2 ≤ q₁ ∧ 2 ≤ q₂ ∧ Int.gcd q₁ q₂ = 1 ∧ q₁ • anom = 0 ∧ q₂ • anom = 0 := by
  exact Omega.anom_oracle_collapse anom

end Omega.POM
