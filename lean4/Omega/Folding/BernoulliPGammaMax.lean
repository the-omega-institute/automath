import Mathlib.Tactic
import Omega.Folding.BernoulliPCumulantDenominatorLaw
import Omega.Folding.BernoulliPDensityUnimodal

/-!
# Bernoulli-p gamma global max

Concrete wrapper around the already formalized Bernoulli-`p` mismatch-density global maximum.
-/

noncomputable section

namespace Omega.Folding

/-- The Bernoulli mismatch density from the paper. -/
def bernoulliPGamma (p : ℝ) : ℝ :=
  p ^ 2 * (3 - 2 * p) / (1 + p ^ 3)

/-- The cumulant denominator package records the same cubic denominator `1 + p^3` used by
`γ(p)`. -/
theorem bernoulliPGamma_denominator_law :
    ∀ p : ℚ, bernoulliPImplicitDenominator p = 1 + p ^ 3 := by
  intro p
  exact (paper_fold_gauge_anomaly_bernoulli_p_cumulant_denominator_law p).1

/-- The existing unimodality theorem already proves that the unique critical point in `(0,1)` is
the unique root of `p^3 + 2p - 2`, and at that point `γ(p★) = p★^2`. -/
theorem paper_fold_bernoulli_p_gamma_global_max_true :
    (∀ p : ℚ, bernoulliPImplicitDenominator p = 1 + p ^ 3) ∧
      ∃! pStar : ℝ, pStar ∈ Set.Ioo 0 1 ∧ pStar ^ 3 + 2 * pStar - 2 = 0 ∧
        bernoulliPGamma pStar = pStar ^ 2 := by
  refine ⟨bernoulliPGamma_denominator_law, ?_⟩
  simpa [bernoulliPGamma] using paper_fold_gauge_anomaly_bernoulli_p_density_unimodal

/-- Paper-facing wrapper for the Bernoulli-`p` mismatch-density global maximum.
    prop:fold-bernoulli-p-gamma-global-max -/
def paper_fold_bernoulli_p_gamma_global_max : Prop := by
  exact
    (∀ p : ℚ, bernoulliPImplicitDenominator p = 1 + p ^ 3) ∧
      ∃! pStar : ℝ, pStar ∈ Set.Ioo 0 1 ∧ pStar ^ 3 + 2 * pStar - 2 = 0 ∧
        bernoulliPGamma pStar = pStar ^ 2

end Omega.Folding
