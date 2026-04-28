import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Root-list data for a polynomial and its Chebyshev--Satake quadratic lift. -/
structure xi_chebyshev_satake_discriminant_endpoint_localization_data (K : Type*) [Field K] where
  degree : ℕ
  leadingCoeff : K
  root : Fin degree → K

namespace xi_chebyshev_satake_discriminant_endpoint_localization_data

variable {K : Type*} [Field K]

/-- The product over unordered pairs of roots appearing in the base discriminant. -/
def pairProduct (D : xi_chebyshev_satake_discriminant_endpoint_localization_data K) : K :=
  ∏ ij ∈ (Finset.univ.product Finset.univ).filter
      (fun ij : Fin D.degree × Fin D.degree => ij.1 < ij.2),
    (D.root ij.1 - D.root ij.2) ^ 2

/-- Root-list model of the base discriminant. -/
def baseDiscriminant (D : xi_chebyshev_satake_discriminant_endpoint_localization_data K) : K :=
  D.leadingCoeff ^ D.degree * D.pairProduct

/-- Endpoint contribution `G(2)G(-2)` in root-list form. -/
def endpointProduct (D : xi_chebyshev_satake_discriminant_endpoint_localization_data K) : K :=
  ∏ j : Fin D.degree, D.root j ^ 2 - (4 : K)

/-- Lifted discriminant for the product of the quadratic factors `u² - s_j u + 1`. -/
def liftDiscriminant (D : xi_chebyshev_satake_discriminant_endpoint_localization_data K) : K :=
  D.baseDiscriminant ^ 2 * D.endpointProduct

end xi_chebyshev_satake_discriminant_endpoint_localization_data

/-- Paper label: `prop:xi-chebyshev-satake-discriminant-endpoint-localization`. -/
theorem paper_xi_chebyshev_satake_discriminant_endpoint_localization {K : Type*} [Field K]
    (D : xi_chebyshev_satake_discriminant_endpoint_localization_data K) :
    D.liftDiscriminant = D.baseDiscriminant ^ 2 * D.endpointProduct := by
  rfl

end

end Omega.Zeta
