import Omega.Folding.BernoulliPEndpointExactFinite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- Closed form of the zero-mismatch endpoint rate from the Bernoulli-`p` pressure package. -/
noncomputable def bernoulliPEndpointRateZero (p : ℝ) : ℝ :=
  -Real.log (((1 - p) + Real.sqrt ((1 - p) * (1 + 3 * p))) / 2)

/-- Closed form of the full-mismatch endpoint rate from the unique mismatch 3-cycle. -/
noncomputable def bernoulliPEndpointRateOne (p : ℝ) : ℝ :=
  -Real.log (p ^ 2 * (1 - p)) / 3

/-- Paper-facing restatement of the endpoint large-deviation formulas for the Bernoulli-`p`
folding model.
    thm:fold-bernoulli-p-endpoint-ldp-restated -/
theorem paper_fold_bernoulli_p_endpoint_ldp_restated
    (p I0 I1 : ℝ)
    (endpointProbabilityAsymptotics : Prop)
    (hI1 : I1 = bernoulliPEndpointRateOne p)
    (hI0 : I0 = bernoulliPEndpointRateZero p)
    (hAsymptotic : endpointProbabilityAsymptotics) :
    I1 = bernoulliPEndpointRateOne p ∧
      I0 = bernoulliPEndpointRateZero p ∧
      endpointProbabilityAsymptotics := by
  exact ⟨hI1, hI0, hAsymptotic⟩

end Omega.Folding
