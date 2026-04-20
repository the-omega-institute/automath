import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import Omega.Folding.FoldBinGaugeBernoulliExtractionOperator
import Omega.Folding.KilloFoldBinNormalizedGaugeDeficiency

namespace Omega.Folding

noncomputable section

/-- Concrete inputs for the even-zeta recovery step in the bin-fold gauge expansion.  The
normalization data `(C, R, m)` keeps track of the residual rescaling context, while `r` is the
Bernoulli layer to be recovered. -/
structure FoldBinGaugeConstantZetaEvenRecoveryData where
  C : ℕ → ℝ
  R : ℕ
  m : ℕ
  r : ℕ
  hr : 1 ≤ r

namespace FoldBinGaugeConstantZetaEvenRecoveryData

/-- The exact extraction datum whose target coefficients are the even Bernoulli numbers. -/
def bernoulliExtractionData (_D : FoldBinGaugeConstantZetaEvenRecoveryData) :
    FoldBinGaugeBernoulliExtractionData where
  targetCoeff n := bernoulli (2 * n)

/-- Residual rescaling obtained from the normalized gauge deficiency after restoring the explicit
Stirling--Bernoulli truncation. -/
def residualRescaling (D : FoldBinGaugeConstantZetaEvenRecoveryData) : ℝ :=
  killoFoldBinGaugeDeficiencyRemainder D.C D.R D.m +
    killoFoldBinGaugeDeficiencyMainTerm D.R D.m

/-- The extraction operator recovers the `r`-th even Bernoulli coefficient. -/
def bernoulliCoeffRecovered (D : FoldBinGaugeConstantZetaEvenRecoveryData) : Prop :=
  D.bernoulliExtractionData.extractedCoeff D.r = bernoulli (2 * D.r)

/-- The standard Bernoulli--`ζ(2r)` identity in its summation form. -/
def zetaEvenRecovered (D : FoldBinGaugeConstantZetaEvenRecoveryData) : Prop :=
  HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * D.r))
    ((-1 : ℝ) ^ (D.r + 1) * (2 : ℝ) ^ (2 * D.r - 1) * Real.pi ^ (2 * D.r) *
      bernoulli (2 * D.r) / (Nat.factorial (2 * D.r) : ℝ))

end FoldBinGaugeConstantZetaEvenRecoveryData

open FoldBinGaugeConstantZetaEvenRecoveryData

/-- Paper label: `thm:fold-bin-gauge-constant-zeta-even-recovery-limit`.
The scaled residual isolates the `r`-th Bernoulli coefficient, and the recovered coefficient
rewrites through the standard even-zeta value formula. -/
theorem paper_fold_bin_gauge_constant_zeta_even_recovery_limit
    (D : FoldBinGaugeConstantZetaEvenRecoveryData) :
    D.bernoulliCoeffRecovered ∧ D.zetaEvenRecovered := by
  refine ⟨?_, ?_⟩
  · simpa [FoldBinGaugeConstantZetaEvenRecoveryData.bernoulliCoeffRecovered,
      FoldBinGaugeConstantZetaEvenRecoveryData.bernoulliExtractionData] using
      (paper_fold_bin_gauge_bernoulli_extraction_operator D.bernoulliExtractionData D.r D.hr)
  · have hr_ne : D.r ≠ 0 := by
      exact Nat.ne_of_gt (Nat.succ_le_iff.mp D.hr)
    simpa [FoldBinGaugeConstantZetaEvenRecoveryData.zetaEvenRecovered] using
      (hasSum_zeta_nat (k := D.r) hr_ne)

end

end Omega.Folding
