import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.OperatorAlgebra.FoldIndexExtremalEntropyLossMaxfiber
import Omega.OperatorAlgebra.RenyiLossSpectrumCappedByIndex

namespace Omega.Conclusion

open Omega.OperatorAlgebra
open Omega.OperatorAlgebra.FoldJonesBasicConstructionDirectsum

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]

/-- Order-`q` Rényi loss along a finite fold. In this finite point-mass model the loss is the same
fiber-size logarithm for every integer order, so the all-orders bound is immediate once the
max-fiber formula is known. -/
noncomputable def conclusion_max_fiber_controls_renyi_loss_all_orders_loss
    (fold : Ω → X) (_q : ℕ) (ω : Ω) : ℝ :=
  foldFiberRenyiFlatness fold ω

end

/-- The max-fiber controls every order-`q` point-mass Rényi loss in the finite fold model, and the
`Dmax` endpoint is exactly the logarithm of the largest fiber. -/
def conclusion_max_fiber_controls_renyi_loss_all_orders_statement : Prop :=
  ∀ {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]
    (fold : Ω → X), Function.Surjective fold →
      foldIndexEqualsMaxFiber fold ∧
        (∀ q : ℕ, 2 ≤ q →
          (∀ ω,
            0 ≤ conclusion_max_fiber_controls_renyi_loss_all_orders_loss fold q ω) ∧
              (∀ ω,
                conclusion_max_fiber_controls_renyi_loss_all_orders_loss fold q ω ≤
                  Real.log (foldLargestFiberCard fold))) ∧
        foldDmaxCapacity fold = Real.log (foldLargestFiberCard fold) ∧
        (∀ ω, foldFiberRenyiFlatness fold ω = foldDmaxCapacity fold ↔
          Fintype.card (foldFiber fold (fold ω)) = foldLargestFiberCard fold)

/-- Paper label: `cor:conclusion-max-fiber-controls-renyi-loss-all-orders`. -/
theorem paper_conclusion_max_fiber_controls_renyi_loss_all_orders :
    conclusion_max_fiber_controls_renyi_loss_all_orders_statement := by
  intro Ω X _ _ _ _ _ fold hfold
  rcases paper_op_algebra_index_extremal_entropy_loss_maxfiber fold hfold with
    ⟨hIndex, _, hChar⟩
  rcases paper_op_algebra_renyi_loss_spectrum_capped_by_index fold hfold with
    ⟨hNonneg, hUpper, hDmax⟩
  refine ⟨hIndex, ?_, hDmax, ?_⟩
  · intro q hq
    refine ⟨?_, ?_⟩
    · intro ω
      simpa [conclusion_max_fiber_controls_renyi_loss_all_orders_loss] using hNonneg ω
    · intro ω
      simpa [conclusion_max_fiber_controls_renyi_loss_all_orders_loss] using hUpper ω
  · intro ω
    rw [hDmax]
    exact hChar.2 ω
