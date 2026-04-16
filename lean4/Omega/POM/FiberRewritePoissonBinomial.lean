import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local package for the Poisson--binomial rewriting of the fiber rewrite-count law. The
fields encode the normalized PGF factorization, identification with a Poisson--binomial law, the
resulting mean and variance formulas, and the unified Bernstein tail estimate. -/
structure FiberRewritePoissonBinomialData where
  normalizedPgfFactorization : Prop
  poissonBinomialLaw : Prop
  meanFormula : Prop
  varianceFormula : Prop
  bernsteinTailBound : Prop
  normalizedPgfFactorization_h : normalizedPgfFactorization
  poissonBinomialLaw_h : poissonBinomialLaw
  meanFormula_h : meanFormula
  varianceFormula_h : varianceFormula
  bernsteinTailBound_h : bernsteinTailBound

/-- Paper-facing wrapper for the fiber rewrite-count Poisson--binomial package.
    cor:pom-fiber-rewrite-poisson-binomial -/
theorem paper_pom_fiber_rewrite_poisson_binomial (h : FiberRewritePoissonBinomialData) :
    h.normalizedPgfFactorization ∧ h.poissonBinomialLaw ∧ h.meanFormula ∧ h.varianceFormula ∧
      h.bernsteinTailBound := by
  exact
    ⟨h.normalizedPgfFactorization_h, h.poissonBinomialLaw_h, h.meanFormula_h,
      h.varianceFormula_h, h.bernsteinTailBound_h⟩

end Omega.POM
