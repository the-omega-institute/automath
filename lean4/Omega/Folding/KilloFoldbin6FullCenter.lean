import Mathlib.Tactic
import Omega.Folding.BinFold
import Omega.Folding.BoundaryLayer

namespace Omega

/-- The eight minimal multiplicity fibers at window size `6`. -/
def foldbin6FullCenterInvolutionCount : Nat :=
  cBinFiberHist 6 2

/-- The three boundary generators singled out in the window-`6` audit. -/
def foldbin6FullCenterBoundaryGenerators : Nat :=
  cBoundaryCount 6

/-- Removing the boundary generators leaves rank `5`. -/
def foldbin6FullCenterResidualRank : Nat :=
  foldbin6FullCenterInvolutionCount - foldbin6FullCenterBoundaryGenerators

/-- Paper label: `thm:killo-foldbin6-full-center`.

The existing window-`6` histogram already shows that exactly eight fibers have the minimal
multiplicity `2`, while the boundary audit contributes exactly three generators.  Their difference
is the residual center rank. -/
theorem paper_killo_foldbin6_full_center :
    foldbin6FullCenterInvolutionCount = 8 ∧
      foldbin6FullCenterBoundaryGenerators = 3 ∧
      foldbin6FullCenterResidualRank = 5 := by
  refine ⟨binFold_boundary_count_m6, cBoundaryCount_six, ?_⟩
  dsimp [foldbin6FullCenterResidualRank, foldbin6FullCenterInvolutionCount,
    foldbin6FullCenterBoundaryGenerators]
  rw [binFold_boundary_count_m6, cBoundaryCount_six]

end Omega
