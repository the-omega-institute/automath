import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete residual/enumerative asymptotic data for the double-KL complexity comparison. The two
rates are written using their limiting KL constants and the corresponding `γ`-terms, and the
boundary and residual `γ`-terms are assumed to match. -/
structure conclusion_double_kl_residual_conditional_complexity_identity_data where
  residualRate : ℝ
  enumerativeRate : ℝ
  residualKlConstant : ℝ
  boundaryKlConstant : ℝ
  residualGamma : ℝ
  boundaryGamma : ℝ
  residualRate_eq :
    residualRate = residualKlConstant - residualGamma
  enumerativeRate_eq :
    enumerativeRate = boundaryKlConstant - boundaryGamma
  sharedGamma_eq : residualGamma = boundaryGamma

namespace conclusion_double_kl_residual_conditional_complexity_identity_data

/-- Residual complexity rate expressed through the residual KL constant and the common
`γ`-correction. -/
def residual_rate_formula
    (h : conclusion_double_kl_residual_conditional_complexity_identity_data) : Prop :=
  h.residualRate = h.residualKlConstant - h.residualGamma

/-- Boundary-uniform enumerative rate expressed through the boundary KL constant and the same
`γ`-correction. -/
def enumerative_rate_formula
    (h : conclusion_double_kl_residual_conditional_complexity_identity_data) : Prop :=
  h.enumerativeRate = h.boundaryKlConstant - h.boundaryGamma

/-- The exact gap between the two rates is the gap of the limiting KL constants once the common
`γ`-term is cancelled. -/
def rate_gap_formula
    (h : conclusion_double_kl_residual_conditional_complexity_identity_data) : Prop :=
  h.residualRate - h.enumerativeRate = h.residualKlConstant - h.boundaryKlConstant

end conclusion_double_kl_residual_conditional_complexity_identity_data

/-- Paper label: `thm:conclusion-double-kl-residual-conditional-complexity-identity`. Rewriting
the residual and enumerative limits through the shared `γ`-terms and subtracting gives the exact
rate-gap identity. -/
theorem paper_conclusion_double_kl_residual_conditional_complexity_identity
    (h : conclusion_double_kl_residual_conditional_complexity_identity_data) :
    h.residual_rate_formula /\ h.enumerative_rate_formula /\ h.rate_gap_formula := by
  refine ⟨h.residualRate_eq, h.enumerativeRate_eq, ?_⟩
  dsimp [conclusion_double_kl_residual_conditional_complexity_identity_data.rate_gap_formula]
  rw [h.residualRate_eq, h.enumerativeRate_eq, h.sharedGamma_eq]
  ring

end Omega.Conclusion
