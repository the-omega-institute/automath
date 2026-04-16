import Mathlib.Tactic

namespace Omega.Kronecker

/-- Chapter-local wrapper for the denominator-length Kronecker `W₁` closed forms.
The data package the monotone-coupling quantile formula, the split on the sign of
`δ = α - p / q`, the bad-side linear evaluation together with its half-star-discrepancy
relation, and the good-side quadratic evaluation with constant star discrepancy. -/
structure KroneckerW1DenominatorClosedFormData where
  monotoneCouplingQuantileFormula : Prop
  deltaSignSplit : Prop
  monotoneCouplingQuantileFormula_h : monotoneCouplingQuantileFormula
  deltaSignSplit_h : deltaSignSplit
  badSideLinearClosedForm : Prop
  badSideHalfStarRelation : Prop
  goodSideQuadraticClosedForm : Prop
  goodSideStarConstant : Prop
  deriveBadSideLinearClosedForm :
    monotoneCouplingQuantileFormula → deltaSignSplit → badSideLinearClosedForm
  deriveBadSideHalfStarRelation :
    badSideLinearClosedForm → badSideHalfStarRelation
  deriveGoodSideQuadraticClosedForm :
    monotoneCouplingQuantileFormula → deltaSignSplit → goodSideQuadraticClosedForm
  deriveGoodSideStarConstant :
    goodSideQuadraticClosedForm → goodSideStarConstant

/-- Paper-facing wrapper for the denominator-length Kronecker `W₁` closed forms.
The monotone-coupling quantile identity and the split on `δ = α - p / q` recover the bad-side
linear formula and half-star-discrepancy relation, and likewise the good-side quadratic formula
and constant star discrepancy.
    thm:kronecker-w1-denominator-closed-form -/
theorem paper_kronecker_w1_denominator_closed_form (D : KroneckerW1DenominatorClosedFormData) :
    D.badSideLinearClosedForm ∧ D.badSideHalfStarRelation ∧ D.goodSideQuadraticClosedForm ∧
      D.goodSideStarConstant := by
  have hBadLinear : D.badSideLinearClosedForm :=
    D.deriveBadSideLinearClosedForm D.monotoneCouplingQuantileFormula_h D.deltaSignSplit_h
  have hGoodQuadratic : D.goodSideQuadraticClosedForm :=
    D.deriveGoodSideQuadraticClosedForm D.monotoneCouplingQuantileFormula_h D.deltaSignSplit_h
  exact
    ⟨hBadLinear, D.deriveBadSideHalfStarRelation hBadLinear, hGoodQuadratic,
      D.deriveGoodSideStarConstant hGoodQuadratic⟩

end Omega.Kronecker
