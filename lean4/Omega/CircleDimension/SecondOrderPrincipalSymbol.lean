import Mathlib

namespace Omega.CircleDimension

open scoped BigOperators

/-- Concrete finite-dimensional data for a second-order principal symbol package. The Hessian
controls the quadratic term, and the long-time/small-parameter remainder is forced to vanish at the
principal-symbol scale. -/
structure SecondOrderPrincipalSymbolData where
  dim : ℕ
  hessian : Fin dim → Fin dim → ℝ
  symbol : (Fin dim → ℝ) → ℝ
  longTimeScale : ℝ
  smallParameter : ℝ
  expansion :
    ∀ ξ : Fin dim → ℝ,
      symbol ξ =
        (∑ i : Fin dim, ∑ j : Fin dim, hessian i j * ξ i * ξ j) +
          longTimeScale * smallParameter
  smallParameter_eq_zero : smallParameter = 0
  positive_hessian :
    ∀ ξ : Fin dim → ℝ, ξ ≠ 0 →
      0 < ∑ i : Fin dim, ∑ j : Fin dim, hessian i j * ξ i * ξ j

namespace SecondOrderPrincipalSymbolData

/-- The quadratic form extracted from the audited Hessian. -/
def principalQuadraticForm (D : SecondOrderPrincipalSymbolData) (ξ : Fin D.dim → ℝ) : ℝ :=
  ∑ i : Fin D.dim, ∑ j : Fin D.dim, D.hessian i j * ξ i * ξ j

/-- The principal symbol is exactly the Hessian quadratic form, and positivity of that quadratic
form gives the nondegeneracy package. -/
def HasQuadraticPrincipalSymbol (D : SecondOrderPrincipalSymbolData) : Prop :=
  (∀ ξ : Fin D.dim → ℝ, D.symbol ξ = D.principalQuadraticForm ξ) ∧
    ∀ ξ : Fin D.dim → ℝ, ξ ≠ 0 → 0 < D.principalQuadraticForm ξ

end SecondOrderPrincipalSymbolData

/-- Paper label: `prop:cdim-second-order-principal-symbol`. Packaging the Hessian together with the
vanishing small-parameter remainder identifies the principal symbol with its quadratic part, and
the positivity hypothesis provides nondegeneracy. -/
theorem paper_cdim_second_order_principal_symbol (D : SecondOrderPrincipalSymbolData) :
    D.HasQuadraticPrincipalSymbol := by
  refine ⟨?_, ?_⟩
  · intro ξ
    simpa [SecondOrderPrincipalSymbolData.principalQuadraticForm, D.smallParameter_eq_zero] using
      D.expansion ξ
  · intro ξ hξ
    simpa [SecondOrderPrincipalSymbolData.principalQuadraticForm] using D.positive_hessian ξ hξ

end Omega.CircleDimension
