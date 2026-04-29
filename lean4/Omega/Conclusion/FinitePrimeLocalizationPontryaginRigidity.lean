import Omega.CircleDimension.LocalizationHomCategoryClassification
import Omega.Zeta.LocalizedIntegersOrderDualQuotient

namespace Omega.Conclusion

open Omega.CircleDimension
open Omega.Zeta

/-- Paper label: `thm:conclusion-finite-prime-localization-pontryagin-rigidity`. -/
theorem paper_conclusion_finite_prime_localization_pontryagin_rigidity
    (S T : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p) :
    (Nonempty (localizedIsoScalar S T) ↔
        Nonempty (SupportedLocalizedIntegerGroup S ≃+ SupportedLocalizedIntegerGroup T)) ∧
      (Nonempty (SupportedLocalizedIntegerGroup S ≃+ SupportedLocalizedIntegerGroup T) ↔
        S = T) := by
  let D : LocalizedGsEmbeddingOrderData :=
    { S := S
      T := T
      S_primes := hS
      T_primes := hT }
  have hScalar :
      Nonempty (localizedIsoScalar S T) ↔ S = T :=
    (paper_xi_cdim_localization_hom_category_classification D).2.2.2.2
  have hGroup :
      Nonempty (SupportedLocalizedIntegerGroup S ≃+ SupportedLocalizedIntegerGroup T) ↔ S = T :=
    (paper_xi_localized_integers_order_dual_quotient S T hS hT).2.2.2
  refine ⟨?_, hGroup⟩
  exact hScalar.trans hGroup.symm

end Omega.Conclusion
