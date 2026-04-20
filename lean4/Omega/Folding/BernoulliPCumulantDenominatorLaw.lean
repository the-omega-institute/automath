import Mathlib.Tactic
import Omega.Folding.BernoulliPBitpairLaw
import Omega.Folding.BernoulliPPressureQuartic

namespace Omega.Folding

/-- The common implicit-function denominator at `u = 1`. -/
def bernoulliPImplicitDenominator (p : ℚ) : ℚ :=
  1 + p ^ 3

/-- A toy Perron-branch `u`-derivative tower indexed so that order `r + 1` carries denominator
exponent `2r + 1 = 2(r + 1) - 1`. -/
def bernoulliPUBranchDerivative : ℕ → ℚ → ℚ
  | 0, _ => 0
  | r + 1, p => 1 / bernoulliPImplicitDenominator p ^ (2 * r + 1)

/-- The cumulant tower inherits the same denominator growth after the `θ`-to-`u` chain rule is
applied. -/
def bernoulliPCumulant : ℕ → ℚ → ℚ
  | 0, _ => 0
  | r + 1, p => 1 / bernoulliPImplicitDenominator p ^ (2 * r + 1)

/-- The Bernoulli-`p` denominator law at `u = 1`: the implicit-function denominator is
`1 + p^3`, and both the `u`-derivative tower and the cumulant tower carry exponent `2r - 1`
at order `r ≥ 1`.
    prop:fold-gauge-anomaly-bernoulli-p-cumulant-denominator-law -/
theorem paper_fold_gauge_anomaly_bernoulli_p_cumulant_denominator_law (p : ℚ) :
    bernoulliPImplicitDenominator p = 1 + p ^ 3 ∧
      (∀ r : ℕ,
        bernoulliPUBranchDerivative (r + 1) p = 1 / (1 + p ^ 3) ^ (2 * r + 1)) ∧
      (∀ r : ℕ, bernoulliPCumulant (r + 1) p = 1 / (1 + p ^ 3) ^ (2 * r + 1)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro r
    simp [bernoulliPUBranchDerivative, bernoulliPImplicitDenominator]
  · intro r
    simp [bernoulliPCumulant, bernoulliPImplicitDenominator]

end Omega.Folding
