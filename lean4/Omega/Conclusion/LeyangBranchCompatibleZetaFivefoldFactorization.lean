import Mathlib.Tactic

namespace Omega.Conclusion

open Finset

/-- Concrete data for the five Lee--Yang branch sheets: each sheet has local fixed-point
counts and a local zeta factor, and the global object is the disjoint union/product package. -/
structure conclusion_leyang_branch_compatible_zeta_fivefold_factorization_data where
  conclusion_leyang_branch_compatible_zeta_fivefold_factorization_localFixed :
    Fin 5 → ℕ → ℕ
  conclusion_leyang_branch_compatible_zeta_fivefold_factorization_totalFixed : ℕ → ℕ
  conclusion_leyang_branch_compatible_zeta_fivefold_factorization_localZeta :
    Fin 5 → ℚ → ℚ
  conclusion_leyang_branch_compatible_zeta_fivefold_factorization_totalZeta : ℚ → ℚ
  conclusion_leyang_branch_compatible_zeta_fivefold_factorization_fixed_additivity :
    ∀ n : ℕ,
      conclusion_leyang_branch_compatible_zeta_fivefold_factorization_totalFixed n =
        ∑ i : Fin 5,
          conclusion_leyang_branch_compatible_zeta_fivefold_factorization_localFixed i n
  conclusion_leyang_branch_compatible_zeta_fivefold_factorization_zeta_product :
    ∀ z : ℚ,
      conclusion_leyang_branch_compatible_zeta_fivefold_factorization_totalZeta z =
        ∏ i : Fin 5,
          conclusion_leyang_branch_compatible_zeta_fivefold_factorization_localZeta i z

/-- The five-sheet zeta factorization, including the equal-local-map specialization. -/
def conclusion_leyang_branch_compatible_zeta_fivefold_factorization_statement
    (D : conclusion_leyang_branch_compatible_zeta_fivefold_factorization_data) : Prop :=
  (∀ n : ℕ,
      D.conclusion_leyang_branch_compatible_zeta_fivefold_factorization_totalFixed n =
        ∑ i : Fin 5,
          D.conclusion_leyang_branch_compatible_zeta_fivefold_factorization_localFixed i n) ∧
    (∀ z : ℚ,
      D.conclusion_leyang_branch_compatible_zeta_fivefold_factorization_totalZeta z =
        ∏ i : Fin 5,
          D.conclusion_leyang_branch_compatible_zeta_fivefold_factorization_localZeta i z) ∧
    (∀ localMap : ℚ → ℚ,
      (∀ i : Fin 5, ∀ z : ℚ,
        D.conclusion_leyang_branch_compatible_zeta_fivefold_factorization_localZeta i z =
          localMap z) →
        ∀ z : ℚ,
          D.conclusion_leyang_branch_compatible_zeta_fivefold_factorization_totalZeta z =
            localMap z ^ 5)

/-- Paper label: `prop:conclusion-leyang-branch-compatible-zeta-fivefold-factorization`. -/
theorem paper_conclusion_leyang_branch_compatible_zeta_fivefold_factorization
    (D : conclusion_leyang_branch_compatible_zeta_fivefold_factorization_data) :
    conclusion_leyang_branch_compatible_zeta_fivefold_factorization_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · exact D.conclusion_leyang_branch_compatible_zeta_fivefold_factorization_fixed_additivity
  · exact D.conclusion_leyang_branch_compatible_zeta_fivefold_factorization_zeta_product
  · intro localMap hlocal z
    rw [D.conclusion_leyang_branch_compatible_zeta_fivefold_factorization_zeta_product z]
    calc
      (∏ i : Fin 5,
          D.conclusion_leyang_branch_compatible_zeta_fivefold_factorization_localZeta i z) =
          ∏ _i : Fin 5, localMap z := by
            exact prod_congr rfl (fun i _hi => hlocal i z)
      _ = localMap z ^ 5 := by
            simp [prod_const]

end Omega.Conclusion
