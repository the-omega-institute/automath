import Mathlib.Tactic
import Omega.Folding.BinFold
import Omega.Folding.BoundaryLayer
import Omega.Conclusion.Window6MinimalShellRigidSubcoverRootSlice

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

/-- Concrete boundary/interior split of the eight window-`6` center generators. -/
def killo_foldbin6_center_boundary_interior_statement : Prop :=
  Omega.Conclusion.window6BoundaryFiber = {Omega.Conclusion.w100001, Omega.Conclusion.w100101,
      Omega.Conclusion.w101001} ∧
    Omega.Conclusion.window6CyclicFiber = {Omega.Conclusion.w000001, Omega.Conclusion.w010001,
      Omega.Conclusion.w001001, Omega.Conclusion.w000101, Omega.Conclusion.w010101} ∧
    foldbin6FullCenterBoundaryGenerators = Omega.Conclusion.window6BoundaryFiber.card ∧
    foldbin6FullCenterResidualRank = Omega.Conclusion.window6CyclicFiber.card ∧
    foldbin6FullCenterInvolutionCount =
      foldbin6FullCenterBoundaryGenerators + foldbin6FullCenterResidualRank

/-- Paper label: `cor:killo-foldbin6-center-boundary-interior`. -/
theorem paper_killo_foldbin6_center_boundary_interior :
    killo_foldbin6_center_boundary_interior_statement := by
  rcases Omega.Conclusion.paper_conclusion_window6_minimal_shell_rigid_subcover_root_slice with
    ⟨_, hboundary, hcyclic, hboundary_card, hcyclic_card, _⟩
  rcases paper_killo_foldbin6_full_center with ⟨hfull, hboundary_gen, hresidual⟩
  refine ⟨hboundary, hcyclic, ?_, ?_, ?_⟩
  · rw [hboundary_gen, hboundary_card]
  · rw [hresidual, hcyclic_card]
  · rw [hfull, hboundary_gen, hresidual]

end Omega
