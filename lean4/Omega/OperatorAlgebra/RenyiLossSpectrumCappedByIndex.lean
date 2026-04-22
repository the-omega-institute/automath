import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.OperatorAlgebra.FoldDmaxCapacityEqualsLogIndex

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]

/-- Paper label: `cor:op-algebra-renyi-loss-spectrum-capped-by-index`.
In the finite fold model, every point-mass Rényi loss lies between `0` and the logarithm of the
largest fiber, and the `Dmax` endpoint attains that cap. -/
theorem paper_op_algebra_renyi_loss_spectrum_capped_by_index (fold : Ω → X)
    (hfold : Function.Surjective fold) :
    (∀ ω, 0 ≤ foldFiberRenyiFlatness fold ω) ∧
      (∀ ω, foldFiberRenyiFlatness fold ω ≤ Real.log (foldLargestFiberCard fold)) ∧
      foldDmaxCapacity fold = Real.log (foldLargestFiberCard fold) := by
  obtain ⟨hupper, hdmax⟩ := paper_op_algebra_dmax_capacity_equals_log_index fold hfold
  refine ⟨?_, hupper, hdmax⟩
  intro ω
  unfold foldFiberRenyiFlatness
  have hcard_pos : 1 ≤ Fintype.card (foldFiber fold (fold ω)) := by
    exact Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨⟨ω, rfl⟩⟩)
  exact Real.log_nonneg (by exact_mod_cast hcard_pos)

end

end Omega.OperatorAlgebra
