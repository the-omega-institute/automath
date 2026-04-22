import Omega.Conclusion.Window6Collision
import Omega.Conclusion.Window6FirstThreeMomentsRecoverWedderburnType
import Omega.Folding.BinFold

namespace Omega.Folding

/-- Concrete bookkeeping for the audited window-`6` bin-fold groupoid-algebra blocks. -/
structure fold_bin_groupoid_algebra_wedderburn_data where
  witness : Unit := ()

namespace fold_bin_groupoid_algebra_wedderburn_data

/-- The matrix blocks are exactly the `8/4/9` multiplicities of the `2 × 2`, `3 × 3`, and
`4 × 4` fibers. -/
def fold_bin_groupoid_algebra_wedderburn_matrixBlockDecomposition
    (_D : fold_bin_groupoid_algebra_wedderburn_data) : Prop :=
  cBinFiberHist 6 2 = 8 ∧ cBinFiberHist 6 3 = 4 ∧ cBinFiberHist 6 4 = 9

/-- The audited direct sum has finite total dimension and the expected `21` simple blocks. -/
def fold_bin_groupoid_algebra_wedderburn_finiteDimensionalSemisimple
    (_D : fold_bin_groupoid_algebra_wedderburn_data) : Prop :=
  8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2 = 212 ∧
    8 + 4 + 9 = 21

/-- The first three audited moment equations determine the same block multiplicities uniquely. -/
def fold_bin_groupoid_algebra_wedderburn_histogramDeterminesWedderburnBlocks
    (_D : fold_bin_groupoid_algebra_wedderburn_data) : Prop :=
  ∀ {n2 n3 n4 : ℕ},
    n2 + n3 + n4 = 21 →
      2 * n2 + 3 * n3 + 4 * n4 = 64 →
      4 * n2 + 9 * n3 + 16 * n4 = 212 →
      n2 = 8 ∧ n3 = 4 ∧ n4 = 9

end fold_bin_groupoid_algebra_wedderburn_data

local notation "FoldbinGroupoidAlgebraWedderburnData" =>
  fold_bin_groupoid_algebra_wedderburn_data

/-- Paper label: `prop:fold-bin-groupoid-algebra-wedderburn`. -/
theorem paper_fold_bin_groupoid_algebra_wedderburn
    (D : FoldbinGroupoidAlgebraWedderburnData) :
    D.fold_bin_groupoid_algebra_wedderburn_matrixBlockDecomposition ∧
      D.fold_bin_groupoid_algebra_wedderburn_finiteDimensionalSemisimple ∧
      D.fold_bin_groupoid_algebra_wedderburn_histogramDeterminesWedderburnBlocks := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4⟩
  · exact ⟨Omega.Conclusion.window6_S2_wedderburn, Omega.Conclusion.window6_qmoment_triple.1⟩
  · intro n2 n3 n4 h0 h1 h2
    exact
      Omega.Conclusion.paper_conclusion_window6_first_three_moments_recover_wedderburn_type
        h0 h1 h2

end Omega.Folding
