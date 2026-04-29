import Mathlib.Tactic
import Omega.OperatorAlgebra.BlockFoldsatTraceCriterion

namespace Omega.OperatorAlgebra

open FoldPushforwardLiftData

/-- The accepted microstates on the fiber over `x`. -/
def blockFoldsatAcceptedCount (D : FoldPushforwardLiftData) (accept : D.Ω → Bool) (x : D.X) : ℕ :=
  ((D.fiber x).filter fun a => accept a = true).card

/-- Fiberwise denominator-cleared coefficient obtained by multiplying the conditional expectation
by the diagonal Watatani index coefficient `d_x = |fold^{-1}(x)|`. -/
def blockFoldsatWatataniDenominatorClearedCoefficient
    (D : FoldPushforwardLiftData) (accept : D.Ω → Bool) (x : D.X) : ℚ :=
  (D.fiberCard x : ℚ) * D.fiberAverageX (fun a => if accept a then (1 : ℚ) else 0) x

/-- Paper label: `prop:block-foldsat-watatani-denominator-clearing`.
Multiplying the fiber-average acceptance coefficient by the diagonal Watatani index clears the
denominator and recovers the accepted-count trace on that fiber. -/
theorem paper_block_foldsat_watatani_denominator_clearing
    (D : FoldPushforwardLiftData) (accept : D.Ω → Bool) :
    ∀ x : D.X,
      blockFoldsatWatataniDenominatorClearedCoefficient D accept x =
        (blockFoldsatAcceptedCount D accept x : ℚ) := by
  intro x
  have htrace := (paper_block_foldsat_trace_criterion D accept x).2
  have hcard : (D.fiberCard x : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (D.fiberCard_pos x)
  unfold blockFoldsatWatataniDenominatorClearedCoefficient
    blockFoldsatAcceptedCount FoldPushforwardLiftData.fiberAverageX
  calc
    (D.fiberCard x : ℚ) *
        (D.pushforward (fun a => if accept a then (1 : ℚ) else 0) x / D.fiberCard x) =
      D.pushforward (fun a => if accept a then (1 : ℚ) else 0) x := by
        field_simp [hcard]
    _ = (((D.fiber x).filter fun a => accept a = true).card : ℚ) := by
          simpa using htrace

end Omega.OperatorAlgebra
