import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Finite prime-support ledger space of rank `n` over `ℚ`. -/
abbrev conclusion_cofinal_prime_support_no_uniform_bounded_rank_ledger_source
    (n : ℕ) : Type :=
  Fin n → ℚ

/-- A bounded-rank target ledger space of rank `R` over `ℚ`. -/
abbrev conclusion_cofinal_prime_support_no_uniform_bounded_rank_ledger_target
    (R : ℕ) : Type :=
  Fin R → ℚ

/-- Paper label: `thm:conclusion-cofinal-prime-support-no-uniform-bounded-rank-ledger`.
Once the finite prime support has size `R + 1`, no faithful strict additive ledger can land in a
`ℚ`-vector ledger of rank `R`: an injective linear ledger would force `R + 1 ≤ R`. -/
theorem paper_conclusion_cofinal_prime_support_no_uniform_bounded_rank_ledger
    (R : ℕ) :
    ∃ n : ℕ,
      R < n ∧
        ¬ ∃ Φ :
            conclusion_cofinal_prime_support_no_uniform_bounded_rank_ledger_source n →ₗ[ℚ]
              conclusion_cofinal_prime_support_no_uniform_bounded_rank_ledger_target R,
          Function.Injective Φ := by
  refine ⟨R + 1, by omega, ?_⟩
  rintro ⟨Φ, hΦ⟩
  have hdim :=
    LinearMap.finrank_le_finrank_of_injective (R := ℚ) (M := Fin (R + 1) → ℚ)
      (M' := Fin R → ℚ) (f := Φ) hΦ
  simp at hdim

end Omega.Conclusion
