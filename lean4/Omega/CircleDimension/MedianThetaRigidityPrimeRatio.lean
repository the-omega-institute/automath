import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local package for a prime-ratio embedding whose edge labels descend to `Θ`-classes and
whose normalized Gödel code is read off from a path-product expression. -/
structure PrimeRatioEmbeddingPackage where
  V : Type*
  Edge : Type*
  ThetaClass : Type*
  base : V
  edgeTheta : Edge → ThetaClass
  edgePrime : Edge → ℕ
  classRepresentative : ThetaClass → Edge
  representative_spec : ∀ H, edgeTheta (classRepresentative H) = H
  thetaPrime : ThetaClass → ℕ
  squareConsistent : ∀ e, edgePrime e = thetaPrime (edgeTheta e)
  normalizedCode : V → ℕ
  pathProductCode : V → ℕ
  pathIndependent : ∀ v, normalizedCode v = pathProductCode v
  normalizedAtBase : normalizedCode base = 1
  thetaPrime_injective : Function.Injective thetaPrime

/-- An edge-prime labeling induces a `Θ`-class labeling if it is constant on every class. -/
def InducesThetaLabel (P : PrimeRatioEmbeddingPackage) (ι : P.ThetaClass → ℕ) : Prop :=
  ∀ e, P.edgePrime e = ι (P.edgeTheta e)

/-- Paper-facing wrapper for the `Θ`-rigidity package: square-consistent prime-ratio labels descend
to `Θ`-classes, the normalized Gödel code is path-independent, and the induced class labeling is
unique once the base normalization is fixed.
    thm:cdim-median-theta-rigidity-prime-ratio -/
theorem paper_cdim_median_theta_rigidity_prime_ratio (P : PrimeRatioEmbeddingPackage) :
    InducesThetaLabel P P.thetaPrime ∧
    (∀ v, P.normalizedCode v = P.pathProductCode v) ∧
    P.normalizedCode P.base = 1 ∧
    Function.Injective P.thetaPrime ∧
    ∀ ι : P.ThetaClass → ℕ, InducesThetaLabel P ι → ι = P.thetaPrime := by
  refine ⟨P.squareConsistent, P.pathIndependent, P.normalizedAtBase, P.thetaPrime_injective, ?_⟩
  intro ι hι
  funext H
  have hrep₁ : P.edgePrime (P.classRepresentative H) = ι (P.edgeTheta (P.classRepresentative H)) :=
    hι (P.classRepresentative H)
  have hrep₂ :
      P.edgePrime (P.classRepresentative H) = P.thetaPrime (P.edgeTheta (P.classRepresentative H)) :=
    P.squareConsistent (P.classRepresentative H)
  rw [P.representative_spec H] at hrep₁ hrep₂
  exact hrep₁.symm.trans hrep₂

end Omega.CircleDimension
