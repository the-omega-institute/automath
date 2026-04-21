import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Folding

/-- The normalization constant `C_m` appearing in the bin-fold gauge normalization package. -/
noncomputable def killoFoldBinNormalizationConstant (C : ℕ → ℝ) (m : ℕ) : ℝ :=
  C m

/-- The normalized gauge deficiency `Δ_m`. -/
noncomputable def killoFoldBinNormalizedGaugeDeficiency (C : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.log (killoFoldBinNormalizationConstant C m)

/-- The `r`-th Bernoulli coefficient in the Stirling--Bernoulli hierarchy. -/
noncomputable def killoFoldBinBernoulliCoefficient (r : ℕ) : ℝ :=
  ((bernoulli (2 * r) : ℚ) : ℝ) / ((r : ℝ) * (2 * r - 1))

/-- The finite Stirling--Bernoulli truncation used in the normalized gauge-deficiency expansion. -/
noncomputable def killoFoldBinGaugeDeficiencyMainTerm (R m : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 1 R) fun r =>
    killoFoldBinBernoulliCoefficient r *
      (Real.goldenRatio⁻¹ + Real.goldenRatio ^ (2 * r) / Real.goldenRatio ^ 3) *
        (Real.goldenRatio / 2) ^ ((2 * r - 1) * m)

/-- The exact remainder obtained after subtracting the explicit Stirling--Bernoulli truncation. -/
noncomputable def killoFoldBinGaugeDeficiencyRemainder (C : ℕ → ℝ) (R m : ℕ) : ℝ :=
  killoFoldBinNormalizedGaugeDeficiency C m -
    Real.log (2 * Real.pi) - killoFoldBinGaugeDeficiencyMainTerm R m

/-- Paper-facing normalized gauge-deficiency identity: `Δ_m = log C_m`, and after isolating the
finite Stirling--Bernoulli truncation the leftover term is exactly the remainder.
    prop:killo-fold-bin-normalized-gauge-deficiency -/
theorem paper_killo_fold_bin_normalized_gauge_deficiency (C : ℕ → ℝ) (R m : ℕ) :
    killoFoldBinNormalizedGaugeDeficiency C m = Real.log (killoFoldBinNormalizationConstant C m) ∧
      killoFoldBinNormalizedGaugeDeficiency C m =
        Real.log (2 * Real.pi) + killoFoldBinGaugeDeficiencyMainTerm R m +
          killoFoldBinGaugeDeficiencyRemainder C R m := by
  constructor
  · rfl
  · unfold killoFoldBinGaugeDeficiencyRemainder
    ring

end Omega.Folding
