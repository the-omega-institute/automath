import Mathlib.Tactic

namespace Omega.Zeta

open Real

set_option linter.unusedVariables false in
/-- Paper label: `thm:xi-abelian-diffusive-chebotarev-sufficient`.
The diffusive spectral-gap estimate and the corresponding Chebotarev error template
are returned as the two assembled conclusions. -/
theorem paper_xi_abelian_diffusive_chebotarev_sufficient
    (lambda Lambda C c : ℕ → ℝ) (B mainTerm err : ℕ → ℕ → ℝ)
    (h_gap :
      ∀ m, 2 ≤ m → Lambda m ≤ lambda m * Real.exp (-(c m) / (m : ℝ) ^ 2))
    (h_error :
      ∀ m n,
        2 ≤ m →
          |B m n - mainTerm m n| ≤ err m n * Real.exp (-(c m) * (n : ℝ) / (m : ℝ) ^ 2)) :
    (∀ m, 2 ≤ m → Lambda m ≤ lambda m * Real.exp (-(c m) / (m : ℝ) ^ 2)) ∧
      (∀ m n,
        2 ≤ m →
          |B m n - mainTerm m n| ≤
            err m n * Real.exp (-(c m) * (n : ℝ) / (m : ℝ) ^ 2)) := by
  exact ⟨h_gap, h_error⟩

end Omega.Zeta
