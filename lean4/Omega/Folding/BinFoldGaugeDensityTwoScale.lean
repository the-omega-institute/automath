import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.BinFoldGaugeM6
import Omega.Folding.BinGaugeVolumeStirlingSecondOrder
import Omega.Folding.FiberArithmetic

namespace Omega.Folding

/-- The visible two-scale coefficient extracted from the Stirling correction and the last-bit
class count in the bin-fold model. -/
noncomputable def foldBinGaugeTwoScaleCoefficient (m : ℕ) : ℝ :=
  ((Fintype.card (Omega.X m) : ℝ) *
      ((m : ℝ) * Real.log (2 / Real.goldenRatio) + Real.log (2 * Real.pi)) -
    (Nat.fib m : ℝ) * Real.log Real.goldenRatio) / 2 ^ (m + 1)

/-- Concrete two-scale package at the already audited window `m = 6`: histogram support,
Fibonacci cardinalities, and the resulting explicit coefficient extracted from the Stirling/Binet
rewrite used in the paper statement. -/
def foldBinGaugeDensityTwoScale : Prop :=
  cBinFiberHist 6 2 = 8 ∧
    cBinFiberHist 6 3 = 4 ∧
    cBinFiberHist 6 4 = 9 ∧
    8 + 4 + 9 = 21 ∧
    8 * 2 + 4 * 3 + 9 * 4 = 64 ∧
    Fintype.card (Omega.X 6) = Nat.fib 8 ∧
    Fintype.card (Omega.X 6) = 21 ∧
    Nat.fib 6 = 8 ∧
    ((Fintype.card (Omega.X 6) : ℝ) / 2 ^ 7 = (21 : ℝ) / 128) ∧
    ((Nat.fib 6 : ℝ) / 2 ^ 7 = (1 : ℝ) / 16) ∧
    foldBinGaugeTwoScaleCoefficient 6 =
      (21 : ℝ) / 128 *
          (6 * Real.log (2 / Real.goldenRatio) + Real.log (2 * Real.pi)) -
        (1 : ℝ) / 16 * Real.log Real.goldenRatio

/-- The bin-fold gauge-density two-scale coefficient at `m = 6` follows from the verified
window-`6` histogram `2:8, 3:4, 4:9`, the Fibonacci identities `|X₆| = F₈ = 21` and `F₆ = 8`,
and the explicit coefficient extraction obtained by rewriting the Stirling correction term.
    prop:fold-bin-gauge-density-two-scale -/
theorem paper_fold_bin_gauge_density_two_scale : foldBinGaugeDensityTwoScale := by
  refine ⟨cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4, by norm_num, by norm_num, ?_,
    Omega.X.card_X_six, by norm_num, ?_, ?_, ?_⟩
  · simpa using (Omega.X.card_eq_fib 6)
  · rw [Omega.X.card_X_six]
    norm_num
  · norm_num
  · unfold foldBinGaugeTwoScaleCoefficient
    rw [Omega.X.card_X_six]
    ring_nf

end Omega.Folding
