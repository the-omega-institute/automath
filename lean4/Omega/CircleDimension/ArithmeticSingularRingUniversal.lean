import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The arithmetic singular ring presented as a fiber product. -/
def arithmeticSingularRingFiberProduct {Sigma TorusFamily Torus : Type*}
    (piSigma : Sigma → Torus) (mu : TorusFamily → Torus) :=
  { z : Sigma × TorusFamily // piSigma z.1 = mu z.2 }

/-- The left projection from the arithmetic singular ring fiber product. -/
def arithmeticSingularRingFst {Sigma TorusFamily Torus : Type*}
    (piSigma : Sigma → Torus) (mu : TorusFamily → Torus) :
    arithmeticSingularRingFiberProduct piSigma mu → Sigma :=
  fun z => z.1.1

/-- The right projection from the arithmetic singular ring fiber product. -/
def arithmeticSingularRingSnd {Sigma TorusFamily Torus : Type*}
    (piSigma : Sigma → Torus) (mu : TorusFamily → Torus) :
    arithmeticSingularRingFiberProduct piSigma mu → TorusFamily :=
  fun z => z.1.2

/-- The canonical factorization determined by a compatible pair of maps into the two legs of the
fiber product. -/
def arithmeticSingularRingGamma {G Sigma TorusFamily Torus : Type*}
    (piSigma : Sigma → Torus) (mu : TorusFamily → Torus)
    (alpha : G → Sigma) (beta : G → TorusFamily)
    (hcompat : ∀ g, piSigma (alpha g) = mu (beta g)) :
    G → arithmeticSingularRingFiberProduct piSigma mu :=
  fun g => ⟨(alpha g, beta g), hcompat g⟩

/-- Universal factorization property of the arithmetic singular ring fiber product. -/
def arithmeticSingularRingUniversalFactorization {G Sigma TorusFamily Torus : Type*}
    (piSigma : Sigma → Torus) (mu : TorusFamily → Torus)
    (alpha : G → Sigma) (beta : G → TorusFamily)
    (_hcompat : ∀ g, piSigma (alpha g) = mu (beta g)) : Prop :=
  ∃! gamma : G → arithmeticSingularRingFiberProduct piSigma mu,
    arithmeticSingularRingFst piSigma mu ∘ gamma = alpha ∧
      arithmeticSingularRingSnd piSigma mu ∘ gamma = beta

/-- The arithmetic singular ring is the fiber product of the global and primewise phase maps: any
compatible pair of maps factors through it uniquely by taking the pair pointwise.
    prop:cdim-arithmetic-singular-ring-universal -/
theorem paper_cdim_arithmetic_singular_ring_universal
    {G Sigma TorusFamily Torus : Type*}
    (piSigma : Sigma → Torus) (mu : TorusFamily → Torus)
    (alpha : G → Sigma) (beta : G → TorusFamily)
    (hcompat : ∀ g, piSigma (alpha g) = mu (beta g)) :
    arithmeticSingularRingUniversalFactorization piSigma mu alpha beta hcompat := by
  refine ⟨arithmeticSingularRingGamma piSigma mu alpha beta hcompat, ?_, ?_⟩
  · constructor
    · funext g
      rfl
    · funext g
      rfl
  · intro gamma hgamma
    funext g
    apply Subtype.ext
    apply Prod.ext
    · simpa [Function.comp, arithmeticSingularRingFst] using congrFun hgamma.1 g
    · simpa [Function.comp, arithmeticSingularRingSnd] using congrFun hgamma.2 g

end Omega.CircleDimension
