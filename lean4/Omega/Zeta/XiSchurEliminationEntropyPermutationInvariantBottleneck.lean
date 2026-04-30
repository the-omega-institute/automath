import Mathlib

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `prop:xi-schur-elimination-entropy-permutation-invariant-bottleneck`.
If a Schur-elimination entropy is the average of a finite list of step costs, then any
permutation-invariant replacement with the same total has the same average, and at least one
step reaches the average. -/
theorem paper_xi_schur_elimination_entropy_permutation_invariant_bottleneck {κ : ℕ}
    (hκ : 0 < κ) (step : Fin κ → ℝ) (closed : ℝ)
    (havg : (∑ m, step m) / (κ : ℝ) = closed) :
    (∀ step' : Fin κ → ℝ, (∑ m, step' m) = (∑ m, step m) →
      (∑ m, step' m) / (κ : ℝ) = closed) ∧
    ∃ m : Fin κ, closed ≤ step m := by
  constructor
  · intro step' hsum
    simpa [hsum] using havg
  · by_contra hnone
    push_neg at hnone
    have hle : ∀ m ∈ (Finset.univ : Finset (Fin κ)), step m ≤ closed := by
      intro m _
      exact le_of_lt (hnone m)
    have hlt : ∃ m ∈ (Finset.univ : Finset (Fin κ)), step m < closed := by
      exact ⟨⟨0, hκ⟩, by simp, hnone ⟨0, hκ⟩⟩
    have hsum_lt : (∑ m, step m) < ∑ _m : Fin κ, closed := by
      exact Finset.sum_lt_sum hle hlt
    have hconst : (∑ _m : Fin κ, closed) = (κ : ℝ) * closed := by
      simp
    have hsum_eq : (∑ m, step m) = (κ : ℝ) * closed := by
      have hκ' : (κ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hκ)
      simpa [mul_comm] using (div_eq_iff hκ').mp havg
    rw [hconst, hsum_eq] at hsum_lt
    exact lt_irrefl ((κ : ℝ) * closed) hsum_lt

end Omega.Zeta
