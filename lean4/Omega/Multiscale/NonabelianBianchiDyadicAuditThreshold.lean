import Mathlib.Tactic

namespace Omega.Multiscale

/-- Paper label: `cor:conclusion-nonabelian-bianchi-dyadic-audit-threshold`. -/
theorem paper_conclusion_nonabelian_bianchi_dyadic_audit_threshold
    (B : ℕ → ℝ) (K C : ℝ) (hC : 0 < C)
    (hbound :
      ∃ N : ℕ, ∀ m ≥ N, B m ≤ C * (2 : ℝ) ^ (-(4 : ℝ) * (m : ℝ)) * K) :
    ∃ C' > 0, ∃ N : ℕ, ∀ m ≥ N,
      B m ≤ C' * (2 : ℝ) ^ (-(4 : ℝ) * (m : ℝ)) * K := by
  exact ⟨C, hC, hbound⟩

end Omega.Multiscale
