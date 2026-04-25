import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Zeta.XiAddressableGodelProductLowerBoundClassification

namespace Omega.Zeta

/-- The canonical binary chain-interior valuation uses `0` on `false` and `1` on `true`. -/
def xi_chain_interior_godel_average_budget_optimality_canonicalValuation
    {T : ℕ} (_t : Fin T) (a : Fin 2) : ℕ :=
  a.1

lemma xi_chain_interior_godel_average_budget_optimality_canonical_total {T : ℕ} :
    xi_addressable_godel_product_lower_bound_classification_valuation_total
        (xi_chain_interior_godel_average_budget_optimality_canonicalValuation (T := T)) =
      xi_addressable_godel_product_lower_bound_classification_minimal_total 2 T := by
  unfold xi_addressable_godel_product_lower_bound_classification_valuation_total
    xi_chain_interior_godel_average_budget_optimality_canonicalValuation
    xi_addressable_godel_product_lower_bound_classification_minimal_total
  rw [Fintype.sum_prod_type]
  simp

/-- The chain-interior Boolean model has `2^T` states, the q=`2` addressable valuation total is
bounded below by `T`, and the canonical squarefree valuation attains that lower bound exactly. -/
def xi_chain_interior_godel_average_budget_optimality_statement : Prop :=
  ∀ T : ℕ,
    Fintype.card (Finset (Fin T)) = 2 ^ T ∧
      (∀ m : Fin T → Fin 2 → ℕ,
        (∀ t a, a.1 ≤ m t a) →
          xi_addressable_godel_product_lower_bound_classification_minimal_total 2 T ≤
            xi_addressable_godel_product_lower_bound_classification_valuation_total m) ∧
      xi_addressable_godel_product_lower_bound_classification_valuation_total
          (xi_chain_interior_godel_average_budget_optimality_canonicalValuation (T := T)) =
        xi_addressable_godel_product_lower_bound_classification_minimal_total 2 T

theorem xi_chain_interior_godel_average_budget_optimality_verified :
    xi_chain_interior_godel_average_budget_optimality_statement := by
  intro T
  have hCard : Fintype.card (Finset (Fin T)) = 2 ^ T := by
    simp
  refine ⟨hCard, ?_, xi_chain_interior_godel_average_budget_optimality_canonical_total⟩
  intro m hLower
  exact (paper_xi_addressable_godel_product_lower_bound_classification
    (q := 2) (T := T) m hLower).1

/-- Paper label: `thm:xi-chain-interior-godel-average-budget-optimality`. -/
theorem paper_xi_chain_interior_godel_average_budget_optimality :
    xi_chain_interior_godel_average_budget_optimality_statement :=
  xi_chain_interior_godel_average_budget_optimality_verified

end Omega.Zeta
