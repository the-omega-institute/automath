import Mathlib.GroupTheory.Perm.Sign
import Omega.Folding.BinFoldGaugeM6

namespace Omega.Folding

/-- The sign character on a single symmetric-group factor. -/
def binFoldGaugeFiberSign (d : ℕ) : Equiv.Perm (Fin d) →* ℤˣ :=
  Equiv.Perm.sign

/-- The size of the product of the nontrivial sign quotients at the audited window `m = 6`. -/
def binFoldGaugeSignAbelianizationSizeSix : ℕ :=
  2 ^ cBinFiberHist 6 2 * 2 ^ cBinFiberHist 6 3 * 2 ^ cBinFiberHist 6 4

/-- The BinFold gauge decomposition carries a factorwise sign map, and at `m = 6` the verified
fiber histogram `2:8, 3:4, 4:9` yields `21` independent `ℤ/2ℤ` sign bits.
    cor:fold-bin-gauge-sign -/
theorem paper_fold_bin_gauge_sign :
    (paper_fold_bin_gauge_decomposition 6 ∧
      cBinFiberHist 6 2 = 8 ∧
      cBinFiberHist 6 3 = 4 ∧
      cBinFiberHist 6 4 = 9 ∧
      8 + 4 + 9 = 21) ∧
      cBinFiberHist 6 0 = 0 ∧
      cBinFiberHist 6 1 = 0 ∧
      cBinFiberHist 6 5 = 0 ∧
      binFoldGaugeSignAbelianizationSizeSix = 2 ^ 21 := by
  refine ⟨paper_fold_bin_gauge_m6, cBinFiberHist_6_0, cBinFiberHist_6_1, cBinFiberHist_6_5, ?_⟩
  · unfold binFoldGaugeSignAbelianizationSizeSix
    rw [cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4]
    norm_num

end Omega.Folding
