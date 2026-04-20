import Omega.Folding.BinFoldGaugeDecomposition

namespace Omega.Folding

/-- Paper-facing `m = 6` specialization of the BinFold gauge decomposition together with the
window-`6` histogram counts and their total parity-charge budget.
    cor:fold-bin-gauge-m6 -/
theorem paper_fold_bin_gauge_m6 :
    paper_fold_bin_gauge_decomposition 6 ∧
      cBinFiberHist 6 2 = 8 ∧
      cBinFiberHist 6 3 = 4 ∧
      cBinFiberHist 6 4 = 9 ∧
      8 + 4 + 9 = 21 := by
  refine ⟨paper_fold_bin_gauge_decomposition_spec 6, cBinFiberHist_6_2, cBinFiberHist_6_3,
    cBinFiberHist_6_4, by native_decide⟩

end Omega.Folding
