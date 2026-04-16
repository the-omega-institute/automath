import Mathlib.Tactic
import Omega.GU.Window6CyclicWeightThresholdRootLength
import Omega.GU.Window6B3C3VisibleSupportThreeLeviPlanes

namespace Omega.GU

open Finset

/-- The three boundary words contribute a triple zero weight in the adjoint model. -/
def boundaryZeroWeights : Multiset Weight := ({zeroWeight, zeroWeight, zeroWeight} : Multiset Weight)

/-- The window-6 B₃ adjoint-weight multiset: the 18 nonzero visible weights together with the
three zero-weight boundary words. -/
def b3AdjointWeightMultiset : Multiset Weight :=
  (b3VisibleSupport.erase zeroWeight).1 + boundaryZeroWeights

/-- The window-6 C₃ adjoint-weight multiset: the 18 nonzero visible weights together with the
three zero-weight boundary words. -/
def c3AdjointWeightMultiset : Multiset Weight :=
  (c3VisibleSupport.erase zeroWeight).1 + boundaryZeroWeights

/-- Paper-facing wrapper for the `21 = 18 + 3` adjoint-weight multiset package.
    thm:window6-21-adjoint-weight-multiset -/
theorem paper_window6_21_adjoint_weight_multiset :
    paper_window6_b3c3_visible_support_three_levi_planes ∧
    (b3VisibleSupport.erase zeroWeight).card = 18 ∧
    (c3VisibleSupport.erase zeroWeight).card = 18 ∧
    boundaryZeroWeights.card = 3 ∧
    b3AdjointWeightMultiset.card = 21 ∧
    c3AdjointWeightMultiset.card = 21 ∧
    (∀ w ∈ b3VisibleSupport.erase zeroWeight, w ≠ zeroWeight) ∧
    (∀ w ∈ c3VisibleSupport.erase zeroWeight, w ≠ zeroWeight) := by
  refine ⟨paper_window6_b3c3_visible_support_three_levi_planes_proof, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · intro w hw
    exact (Finset.mem_erase.mp hw).1
  · intro w hw
    exact (Finset.mem_erase.mp hw).1

end Omega.GU
