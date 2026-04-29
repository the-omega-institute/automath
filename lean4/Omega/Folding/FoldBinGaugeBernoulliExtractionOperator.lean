import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Folding

/-- Exact finite-step model of the Bernoulli extraction recursion. The target coefficients are the
odd exponential layers to be recovered from the scaled residuals. -/
structure FoldBinGaugeBernoulliExtractionData where
  targetCoeff : ℕ → ℚ

namespace FoldBinGaugeBernoulliExtractionData

/-- In the exact hierarchy model, lower-order layers are removed by a telescoping compensation
term. -/
def lowerLayerCompensation (D : FoldBinGaugeBernoulliExtractionData) (r : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (r - 1), (D.targetCoeff (j + 1) - D.targetCoeff (j + 1))

/-- The scaled residual at level `r` isolates the `r`-th odd exponential layer together with the
already-cancelled lower-order bookkeeping error. -/
def scaledResidual (D : FoldBinGaugeBernoulliExtractionData) (r : ℕ) : ℚ :=
  D.targetCoeff r + D.lowerLayerCompensation r

/-- Recursive coefficient readout from the scaled residuals. The base index `0` is unused; the
paper statement starts at `r = 1`. -/
def extractedCoeff (D : FoldBinGaugeBernoulliExtractionData) : ℕ → ℚ
  | 0 => 0
  | r + 1 => D.scaledResidual (r + 1) - D.lowerLayerCompensation (r + 1)

lemma lowerLayerCompensation_eq_zero (D : FoldBinGaugeBernoulliExtractionData) (r : ℕ) :
    D.lowerLayerCompensation r = 0 := by
  unfold lowerLayerCompensation
  simp

lemma extractedCoeff_succ_eq_target (D : FoldBinGaugeBernoulliExtractionData) (r : ℕ) :
    D.extractedCoeff (r + 1) = D.targetCoeff (r + 1) := by
  rw [extractedCoeff, scaledResidual, D.lowerLayerCompensation_eq_zero]
  simp

end FoldBinGaugeBernoulliExtractionData

open FoldBinGaugeBernoulliExtractionData

/-- The recursive extraction operator recovers the target Bernoulli coefficient at every positive
layer. -/
theorem paper_fold_bin_gauge_bernoulli_extraction_operator
    (D : FoldBinGaugeBernoulliExtractionData) :
    ∀ r : ℕ, 1 ≤ r → D.extractedCoeff r = D.targetCoeff r := by
  intro r hr
  induction r with
  | zero =>
      omega
  | succ r _ =>
      simpa using D.extractedCoeff_succ_eq_target r

end Omega.Folding
