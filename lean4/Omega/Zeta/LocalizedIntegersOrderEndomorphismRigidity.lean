import Omega.Zeta.LocalizedIntegersEndomorphismAutomorphismExplicit
import Omega.Zeta.LocalizedIntegersOrderDualQuotient

namespace Omega.Zeta

open Omega.CircleDimension

/-- The combined order, dual-quotient, isomorphism, endomorphism, and automorphism rigidity
package for finite prime localizations. -/
def xi_localized_integers_order_endomorphism_rigidity_statement
    (S T : Finset Nat) : Prop :=
  (S ⊆ T ↔
      ∃ φ : SupportedLocalizedIntegerGroup S →+ SupportedLocalizedIntegerGroup T,
        φ (localizedOne S) ≠ 0) ∧
    (S ⊆ T ↔
      ∃ φ : SupportedLocalizedIntegerGroup S →+ SupportedLocalizedIntegerGroup T,
        Function.Injective φ) ∧
    (S ⊆ T ↔ LocalizedGsEmbeddingOrderData.compatibleDualSurjection S T) ∧
    (Nonempty (SupportedLocalizedIntegerGroup S ≃+ SupportedLocalizedIntegerGroup T) ↔
      S = T) ∧
    LocalizedIntegersEndomorphismAutomorphismExplicit S

/-- Paper label: `cor:xi-localized-integers-order-endomorphism-rigidity`. -/
theorem paper_xi_localized_integers_order_endomorphism_rigidity
    (S T : Finset Nat) (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime) :
    xi_localized_integers_order_endomorphism_rigidity_statement S T := by
  rcases paper_xi_localized_integers_order_dual_quotient S T hS hT with
    ⟨hNonzero, hInjective, hDual, hIso⟩
  exact ⟨hNonzero, hInjective, hDual, hIso,
    paper_xi_localized_integers_endomorphism_automorphism_explicit S⟩

end Omega.Zeta
