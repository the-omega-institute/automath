import Omega.Folding.BinFoldGaugeSign
import Omega.Folding.BoundaryLayer

namespace Omega.Folding

/-- The audited window-`6` gauge-decomposition proposition bundled by
`paper_fold_bin_gauge_m6`. -/
private def foldBinGaugeM6Fact : Prop :=
  Omega.Folding.paper_fold_bin_gauge_decomposition 6 ∧
    Omega.cBinFiberHist 6 2 = 8 ∧
    Omega.cBinFiberHist 6 3 = 4 ∧
    Omega.cBinFiberHist 6 4 = 9 ∧
    8 + 4 + 9 = 21

/-- The audited window-`6` sign-package proposition bundled by `paper_fold_bin_gauge_sign`. -/
private def foldBinGaugeSignFact : Prop :=
  foldBinGaugeM6Fact ∧
    Omega.cBinFiberHist 6 0 = 0 ∧
    Omega.cBinFiberHist 6 1 = 0 ∧
    Omega.cBinFiberHist 6 5 = 0 ∧
    Omega.Folding.binFoldGaugeSignAbelianizationSizeSix = 2 ^ 21

/-- Paper-facing package of the audited window-`6` BinFold gauge data together with the three
boundary generators and the eight minimal fibers that isolate the distinguished boundary
`S₂` factors.
    cor:fold-bin-boundary-center-z2 -/
theorem paper_fold_bin_boundary_center_z2 :
    foldBinGaugeM6Fact ∧ foldBinGaugeSignFact ∧
      Omega.cBoundaryCount 6 = 3 ∧ Omega.cBinFiberHist 6 2 = 8 := by
  exact ⟨paper_fold_bin_gauge_m6, paper_fold_bin_gauge_sign, Omega.cBoundaryCount_six,
    Omega.cBinFiberHist_6_2⟩

end Omega.Folding
