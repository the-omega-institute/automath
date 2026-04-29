import Mathlib.Tactic
import Omega.CircleDimension.LocalizationHomCategoryClassification

namespace Omega.CircleDimension

open LocalizedGsEmbeddingOrderData

/-- The self-embedding data for one localization `G_S`. -/
def localizedSelfEmbeddingData (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    LocalizedGsEmbeddingOrderData where
  S := S
  T := S
  S_primes := hS
  T_primes := hS

/-- The localized discrete endomorphisms modeled on multiplication by allowed scalars. -/
abbrev localizedDiscreteEndomorphisms (S : Finset ℕ) := localizedHomScalar S S

/-- The rational discrete endomorphisms modeled as `ℚ`-linear endomorphisms of the one-dimensional
vector space `ℚ`. -/
abbrev rationalDiscreteEndomorphisms := ℚ →ₗ[ℚ] ℚ

/-- Multiplication by a scalar as a rational linear endomorphism. -/
def rationalEndomorphismOfScalar (q : ℚ) : rationalDiscreteEndomorphisms where
  toFun r := q * r
  map_add' x y := by ring
  map_smul' a r := by
    simp [smul_eq_mul, mul_left_comm]

lemma rationalEndomorphism_apply (f : rationalDiscreteEndomorphisms) (r : ℚ) :
    f r = f 1 * r := by
  calc
    f r = f (r • (1 : ℚ)) := by simp
    _ = r • f 1 := by simpa using f.map_smul r (1 : ℚ)
    _ = f 1 * r := by simp [smul_eq_mul, mul_comm]

/-- A rational endomorphism is uniquely determined by the image of `1`. -/
def rationalEndomorphismEquivScalar : rationalDiscreteEndomorphisms ≃ ℚ where
  toFun f := f 1
  invFun := rationalEndomorphismOfScalar
  left_inv f := by
    apply LinearMap.ext
    intro r
    simpa [rationalEndomorphismOfScalar, mul_comm] using (rationalEndomorphism_apply f r).symm
  right_inv q := by
    simp [rationalEndomorphismOfScalar]

/-- Paper label: `thm:cdim-star-endomorphism-localized-degree`. The endomorphisms of the localized
discrete model `ℤ[1/S]` are exactly the admissible localization scalars, and the endomorphisms of
the rational model are exactly multiplication by the image of `1`. -/
theorem paper_cdim_star_endomorphism_localized_degree (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    Nonempty (localizedDiscreteEndomorphisms S ≃ { q : ℚ // inLocalizedGs S q }) ∧
      Nonempty (rationalDiscreteEndomorphisms ≃ ℚ) ∧
      (∀ f : rationalDiscreteEndomorphisms, ∀ r : ℚ, f r = f 1 * r) := by
  have hlocalized :
      Nonempty (localizedDiscreteEndomorphisms S ≃ { q : ℚ // inLocalizedGs S q }) :=
    (paper_xi_cdim_localization_hom_category_classification
      (localizedSelfEmbeddingData S hS)).2.2.1
  refine ⟨hlocalized, ⟨rationalEndomorphismEquivScalar⟩,
    rationalEndomorphism_apply⟩

end Omega.CircleDimension
