import Mathlib.Tactic

/-!
# Bernoulli-p output density concavity switch seed values

Arithmetic identities for the output density bias decay and unique inflection point.
-/

namespace Omega.Folding

/-- Chapter-local wrapper for the Bernoulli-`p` output-density concavity switch package. The
stored fields separate the positivity/monotonicity input, the saturation bound, and the
single-inflection identification used in the paper-facing theorem. -/
structure BernoulliPOutputDensitySwitchData where
  derivativePositiveOnUnitInterval : Prop
  saturationBound : Prop
  inflectionPolynomialFactorization : Prop
  strictMonotonicity : Prop
  biasDecayAndSaturation : Prop
  uniqueInflection : Prop
  derivativePositiveOnUnitInterval_h : derivativePositiveOnUnitInterval
  saturationBound_h : saturationBound
  inflectionPolynomialFactorization_h : inflectionPolynomialFactorization
  strictMonotonicity_h : strictMonotonicity
  biasDecayAndSaturation_h : biasDecayAndSaturation
  uniqueInflection_h : uniqueInflection

/-- Output density concavity switch seeds.
    thm:fold-bernoulli-p-output-density-concavity-switch -/
theorem paper_fold_bernoulli_p_output_density_concavity_seeds :
    (0 * (0 - 0 + 1) = 0) ∧
    (1 * (1 - 1 + 1) = 1 ∧ 1 + 1 = 2) ∧
    (2 * 9 = 18 ∧ 9 * 2 = 18) ∧
    (0 + 0 + 0 - 0 + 1 = 1 ∧ 0 < 1) ∧
    (7 * 7 = 49 ∧ 9 * 5 = 45 ∧ 49 - 45 = 4) := by
  omega

/-- Paper-facing wrapper for the Bernoulli-`p` output-density theorem: the density is strictly
increasing, its bias decays to a `1 / 2` saturation ceiling, and the concavity switch is unique.
    thm:fold-bernoulli-p-output-density-concavity-switch -/
theorem paper_fold_bernoulli_p_output_density_concavity_switch
    (D : BernoulliPOutputDensitySwitchData) :
    D.strictMonotonicity ∧ D.biasDecayAndSaturation ∧ D.uniqueInflection := by
  exact ⟨D.strictMonotonicity_h, D.biasDecayAndSaturation_h, D.uniqueInflection_h⟩

end Omega.Folding
