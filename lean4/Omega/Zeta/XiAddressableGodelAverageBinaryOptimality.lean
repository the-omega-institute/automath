import Omega.Zeta.XiAddressableGodelProductLowerBoundClassification

namespace Omega.Zeta

/-- Paper-facing corollary: the addressable Gödel valuation lower bound, with the binary closed
form of the minimal total.
    cor:xi-addressable-godel-average-binary-optimality -/
theorem paper_xi_addressable_godel_average_binary_optimality
    {q T : ℕ} (m : Fin T → Fin q → ℕ) (hLower : ∀ t a, a.1 ≤ m t a) :
    Omega.Zeta.xi_addressable_godel_product_lower_bound_classification_minimal_total q T ≤
        Omega.Zeta.xi_addressable_godel_product_lower_bound_classification_valuation_total m ∧
      (q = 2 →
        Omega.Zeta.xi_addressable_godel_product_lower_bound_classification_minimal_total q T =
          T) := by
  refine ⟨?_, ?_⟩
  · exact (paper_xi_addressable_godel_product_lower_bound_classification m hLower).1
  · intro hq
    subst q
    simp [xi_addressable_godel_product_lower_bound_classification_minimal_total]

end Omega.Zeta
