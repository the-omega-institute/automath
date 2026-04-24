import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.Basic
import Omega.Folding.GaugeAnomalyClt

namespace Omega.Conclusion

open Filter

/-- Eventual upper bound formulation of a limsup inequality for a real-valued probability
sequence. -/
def conclusion_prime_register_residual_support_clt_quantified_eventualUpper
    (p : ℕ → ℝ) (bound : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ m in atTop, p m ≤ bound + ε

/-- Concrete Gaussian comparison profile used for the quantified support upper bound. -/
noncomputable def conclusion_prime_register_residual_support_clt_quantified_gaussianUpper
    (t : ℝ) : ℝ :=
  Real.exp (-((3 * t) ^ 2) / (2 * ((Omega.Folding.gaugeAnomalyVarianceConstant : ℚ) : ℝ)))

/-- Paper label: `cor:conclusion-prime-register-residual-support-clt-quantified`.
If the support event is bounded by the corresponding `G_m` event after the factor `3` transfer,
then any audited Gaussian upper bound for the `G_m` event transfers to the support event as well. -/
theorem paper_conclusion_prime_register_residual_support_clt_quantified
    (supportTail gaugeTail : ℕ → ℝ) (t : ℝ)
    (htransfer : ∀ m, supportTail m ≤ gaugeTail m)
    (hclt :
      conclusion_prime_register_residual_support_clt_quantified_eventualUpper
        gaugeTail (conclusion_prime_register_residual_support_clt_quantified_gaussianUpper t)) :
    conclusion_prime_register_residual_support_clt_quantified_eventualUpper
      supportTail (conclusion_prime_register_residual_support_clt_quantified_gaussianUpper t) := by
  intro ε hε
  filter_upwards [hclt ε hε] with m hm
  exact le_trans (htransfer m) hm

end Omega.Conclusion
