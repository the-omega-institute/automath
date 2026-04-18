import Mathlib.Tactic
import Omega.Folding.BinFold
import Omega.GU.TerminalFoldbin6TwoPointFiberDirectionSpectrum

namespace Omega.GroupUnification

/-- The boundary extremal stable type from `thm:window6-split-extremal-distance-bridge`, namely
`100001`. -/
def window6SplitBoundaryExtremal : Omega.X 6 :=
  Omega.X.ofNat 6 14

/-- The non-boundary extremal stable type from `thm:window6-split-extremal-distance-bridge`,
namely `010001`. -/
def window6SplitRootExtremal : Omega.X 6 :=
  Omega.X.ofNat 6 15

/-- The two stable values that realize the split extremal distance class. -/
def window6SplitExtremalValues : List Nat :=
  [14, 15]

/-- Both extremal two-point fibers carry the same dyadic XOR direction `111110_2 = 62`. -/
def window6SplitSharedDyadicDirection : Nat :=
  62

/-- The explicit two-point witnesses for the two extremal fibers have the same XOR direction. -/
def window6SplitExtremalWitnessDirection : Prop :=
  14 ^^^ 48 = window6SplitSharedDyadicDirection ∧
    15 ^^^ 49 = window6SplitSharedDyadicDirection

/-- The common dyadic direction class is exactly the extremal pair. -/
def window6SplitExtremalSharedClass : Prop :=
  Omega.GU.terminalFoldbin6FiberValuesByDirection window6SplitSharedDyadicDirection =
    window6SplitExtremalValues

private theorem window6_split_boundary_distance_five :
    Omega.cBinFiberMinHamming 6 window6SplitBoundaryExtremal = 5 := by
  native_decide

private theorem window6_split_root_distance_five :
    Omega.cBinFiberMinHamming 6 window6SplitRootExtremal = 5 := by
  native_decide

/-- The unique distance-`5` window-`6` fibers are the split pair
`{100001, 010001}`, and their explicit two-point witnesses share the dyadic direction
`111110_2 = 62`.
    thm:window6-split-extremal-distance-bridge -/
theorem paper_window6_split_extremal_distance_bridge :
    window6SplitExtremalValues.length = Omega.cBinFiberMinHammingHist 6 5 ∧
      Omega.cBinFiberMinHamming 6 window6SplitBoundaryExtremal = 5 ∧
      Omega.cBinFiberMinHamming 6 window6SplitRootExtremal = 5 ∧
      window6SplitExtremalWitnessDirection ∧
      window6SplitExtremalSharedClass := by
  rcases Omega.GU.paper_terminal_foldbin6_two_point_fiber_direction_spectrum with
    ⟨_, _, _, _, h62, _⟩
  refine ⟨?_, window6_split_boundary_distance_five, window6_split_root_distance_five, ?_, h62⟩
  · rw [Omega.binFiber6_minHamming_hist_5]
    norm_num [window6SplitExtremalValues]
  · unfold window6SplitExtremalWitnessDirection window6SplitSharedDyadicDirection
    exact ⟨by decide, by decide⟩

end Omega.GroupUnification
