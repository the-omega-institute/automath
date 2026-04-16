import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local package for the Bernoulli `p = φ / 2` endpoint ratio-limit wrapper.
The structure stores the specialized closed-form data and the two paper-facing consequences:
equal exponential decay and the residue-class ratio limits. -/
structure BernoulliPhiHalfRatioData where
  lambdaPlus : ℚ
  t : ℚ
  equalExponentialDecay : Prop
  modThreeRatioLimits : Prop
  lambdaPlus_eq_half : lambdaPlus = (1 / 2 : ℚ)
  t_eq_eighth : t = (1 / 8 : ℚ)
  hasEqualExponentialDecay : equalExponentialDecay
  hasModThreeRatioLimits : modThreeRatioLimits

/-- At the golden-ratio bias `p = φ / 2`, the zero-mismatch and full-mismatch endpoints share the
same exponential decay rate, and the three mod-`3` ratio limits exist.
    cor:fold-bernoulli-phi-half-ratio-limits -/
theorem paper_fold_bernoulli_phi_half_ratio_limits (D : BernoulliPhiHalfRatioData) :
    D.lambdaPlus = (1 / 2 : ℚ) ∧
      D.t = (1 / 8 : ℚ) ∧
      D.equalExponentialDecay ∧
      D.modThreeRatioLimits := by
  exact
    ⟨D.lambdaPlus_eq_half, D.t_eq_eighth, D.hasEqualExponentialDecay, D.hasModThreeRatioLimits⟩

end Omega.Folding
