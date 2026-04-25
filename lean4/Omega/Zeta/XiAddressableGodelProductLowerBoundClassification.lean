import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Total valuation mass in the prime-addressed finite model: summing the valuation attached to
each coordinate-symbol class. -/
def xi_addressable_godel_product_lower_bound_classification_valuation_total
    {q T : ℕ} (m : Fin T → Fin q → ℕ) : ℕ :=
  ∑ x : Fin T × Fin q, m x.1 x.2

/-- The minimal possible total valuation mass when each coordinate uses the optimal valuation set
`{0, ..., q - 1}`. -/
def xi_addressable_godel_product_lower_bound_classification_minimal_total (q T : ℕ) : ℕ :=
  T * (q * (q - 1) / 2)

private theorem xi_addressable_godel_product_lower_bound_classification_sum_fin_vals (q : ℕ) :
    (∑ a : Fin q, a.1) = q * (q - 1) / 2 := by
  rw [Finset.sum_fin_eq_sum_range]
  calc
    (∑ x ∈ Finset.range q, if x < q then x else 0) = ∑ x ∈ Finset.range q, x := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      simp [Finset.mem_range.mp hx]
    _ = q * (q - 1) / 2 := Finset.sum_range_id q

/-- Concrete finite-coordinate version of the valuation argument behind the paper statement:
each coordinatewise valuation profile dominates the ordered profile `0, ..., q - 1`, and equality
forces every coordinate to use exactly that profile with no slack.
    thm:xi-addressable-godel-product-lower-bound-classification -/
theorem paper_xi_addressable_godel_product_lower_bound_classification
    {q T : ℕ} (m : Fin T → Fin q → ℕ) (hLower : ∀ t a, a.1 ≤ m t a) :
    xi_addressable_godel_product_lower_bound_classification_minimal_total q T ≤
        xi_addressable_godel_product_lower_bound_classification_valuation_total m ∧
      (xi_addressable_godel_product_lower_bound_classification_valuation_total m =
          xi_addressable_godel_product_lower_bound_classification_minimal_total q T ↔
        ∀ t a, m t a = a.1) := by
  have hpoint : ∀ x : Fin T × Fin q, x.2.1 ≤ m x.1 x.2 := by
    intro x
    exact hLower x.1 x.2
  have hsum :
      (∑ x : Fin T × Fin q, x.2.1) ≤
        xi_addressable_godel_product_lower_bound_classification_valuation_total m := by
    exact Finset.sum_le_sum (fun x _ => hpoint x)
  have hbase :
      (∑ x : Fin T × Fin q, x.2.1) =
        xi_addressable_godel_product_lower_bound_classification_minimal_total q T := by
    rw [xi_addressable_godel_product_lower_bound_classification_minimal_total, Fintype.sum_prod_type]
    simp [xi_addressable_godel_product_lower_bound_classification_sum_fin_vals]
  constructor
  · rw [← hbase, xi_addressable_godel_product_lower_bound_classification_valuation_total]
    exact hsum
  · constructor
    · intro hEq t a
      by_contra hneq
      have hlt :
          (∑ x : Fin T × Fin q, x.2.1) <
            xi_addressable_godel_product_lower_bound_classification_valuation_total m := by
        refine Finset.sum_lt_sum (fun x _ => hpoint x) ?_
        refine ⟨(t, a), by simp, ?_⟩
        exact lt_of_le_of_ne (hLower t a) (Ne.symm hneq)
      have : xi_addressable_godel_product_lower_bound_classification_minimal_total q T <
          xi_addressable_godel_product_lower_bound_classification_minimal_total q T := by
        rw [hbase, hEq] at hlt
        exact hlt
      exact (Nat.lt_irrefl _) this
    · intro hExact
      rw [← hbase, xi_addressable_godel_product_lower_bound_classification_valuation_total]
      refine Finset.sum_congr rfl ?_
      intro x hx
      exact hExact x.1 x.2

end Omega.Zeta
