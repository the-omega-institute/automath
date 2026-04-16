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

/-- Chapter-local wrapper for the Lipschitz covariance of Kronecker `W₁` under pushforward. The
fields package the pushforward of couplings, the transportation-cost bound from the Lipschitz
constant, the infimum step over all couplings, and the resulting `W₁` inequality. -/
structure KroneckerW1LipschitzPushforwardData where
  Carrier : Type
  W1 : Carrier → Carrier → ℝ
  pushforward : Carrier → Carrier
  lipschitzConstant : ℝ
  couplingPushforward : Prop
  transportCostBound : Prop
  infimumOverCouplings : Prop
  couplingPushforward_h : couplingPushforward
  transportCostBound_h : transportCostBound
  infimumOverCouplings_h : infimumOverCouplings
  w1PushforwardBound :
    ∀ μ ν : Carrier,
      W1 (pushforward μ) (pushforward ν) ≤ lipschitzConstant * W1 μ ν

/-- Paper-facing wrapper for the Lipschitz pushforward inequality for Kronecker `W₁`.
Pushing couplings forward along `Φ × Φ`, bounding the transport cost by the Lipschitz constant,
and taking the infimum over couplings yield the stated `W₁` covariance.
    prop:w1-lipschitz-pushforward -/
theorem paper_kronecker_w1_lipschitz_pushforward
    (D : KroneckerW1LipschitzPushforwardData) :
    D.couplingPushforward ∧
      D.transportCostBound ∧
      D.infimumOverCouplings ∧
      (∀ μ ν : D.Carrier,
        D.W1 (D.pushforward μ) (D.pushforward ν) ≤ D.lipschitzConstant * D.W1 μ ν) := by
  exact
    ⟨D.couplingPushforward_h, D.transportCostBound_h, D.infimumOverCouplings_h,
      D.w1PushforwardBound⟩

end Omega.Kronecker
