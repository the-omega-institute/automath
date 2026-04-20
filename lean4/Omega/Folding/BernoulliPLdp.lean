import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.BernoulliPEndpointLdpRestated
import Omega.Folding.BernoulliPLdpCompressedCubicParametrization

namespace Omega.Folding

/-- Concrete Bernoulli-`p` package for the compressed-cubic degeneration at `u = 0` together with
the two endpoint logarithmic rate expressions. -/
def bernoulliPGaugeAnomalyLdpStatement (p : ℝ) : Prop :=
  0 < ((1 - p) + Real.sqrt ((1 - p) * (1 + 3 * p))) / 2 ∧
    0 < p ^ 2 * (1 - p) ∧
    bernoulliPLdpCompressedC p 0 = 1 ∧
    bernoulliPLdpCompressedCubicPolynomial p 0 0 = 0 ∧
    bernoulliPEndpointRateZero p =
      -Real.log (((1 - p) + Real.sqrt ((1 - p) * (1 + 3 * p))) / 2) ∧
    bernoulliPEndpointRateOne p = -Real.log (p ^ 2 * (1 - p)) / 3

/-- The Bernoulli endpoint arguments are positive on `0 < p < 1`, the compressed cubic degenerates
to the matching-subgraph branch at `z = v = 0`, and the endpoint rates are exactly the stored
closed forms. -/
theorem bernoulliPGaugeAnomalyLdpStatement_true (p : ℝ) (hp : 0 < p ∧ p < 1) :
    bernoulliPGaugeAnomalyLdpStatement p := by
  rcases hp with ⟨hp0, hp1⟩
  have hq : 0 < 1 - p := by linarith
  have hsqrt : 0 ≤ Real.sqrt ((1 - p) * (1 + 3 * p)) := Real.sqrt_nonneg _
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · nlinarith
  · have hp_sq : 0 < p ^ 2 := sq_pos_of_ne_zero (ne_of_gt hp0)
    nlinarith
  · simp [bernoulliPLdpCompressedC]
  · simp [bernoulliPLdpCompressedCubicPolynomial, bernoulliPLdpCompressedC]

/-- Paper proposition wrapper for the Bernoulli-`p` gauge-anomaly LDP package.
    prop:fold-gauge-anomaly-bernoulli-p-ldp -/
def paper_fold_gauge_anomaly_bernoulli_p_ldp (p : ℝ) (_hp : 0 < p ∧ p < 1) : Prop := by
  exact bernoulliPGaugeAnomalyLdpStatement p

end Omega.Folding
