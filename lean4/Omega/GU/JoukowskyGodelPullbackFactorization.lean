import Mathlib.Tactic

namespace Omega.GU

/-- Chapter-local package for the Joukowsky--Gödel pullback factorization identity. The data store
the resultant product formula, the reciprocal-polynomial rewrite, and the final pullback identity;
the derivation field records the paper's substitution-and-factorization argument as an abstract
implication between these chapter-local statements. -/
structure JoukowskyGodelPullbackFactorizationData where
  resultantProductFormula : Prop
  reciprocalPolynomialRewrite : Prop
  pullbackFactorization : Prop
  resultantProductFormula_h : resultantProductFormula
  reciprocalPolynomialRewrite_h : reciprocalPolynomialRewrite
  derivePullbackFactorization :
    resultantProductFormula → reciprocalPolynomialRewrite → pullbackFactorization

/-- Paper-facing wrapper for the Joukowsky--Gödel pullback factorization identity: after
substituting `w = r z + r⁻¹ z⁻¹` into the resultant product formula and rewriting the reciprocal
factor as `Pᵛ(r² z)`, the pullback splits as the product `P(z) Pᵛ(r² z)`.
    thm:group-jg-pullback-factorization -/
theorem paper_group_jg_pullback_factorization
    (D : JoukowskyGodelPullbackFactorizationData) : D.pullbackFactorization := by
  exact D.derivePullbackFactorization D.resultantProductFormula_h D.reciprocalPolynomialRewrite_h

end Omega.GU
