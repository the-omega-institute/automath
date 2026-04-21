import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.OperatorAlgebra.FoldIndexExtremalEntropyLossMaxfiber

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]

/-- Finite-model `Dmax` capacity of a fold, realized as the worst point-mass Rényi flatness. -/
noncomputable def foldDmaxCapacity (fold : Ω → X) : ℝ :=
  sSup (Set.range (foldFiberRenyiFlatness fold))

private lemma foldFiber_card_pos_at_point {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X]
    [DecidableEq X] (fold : Ω → X) (ω : Ω) :
    0 < Fintype.card (foldFiber fold (fold ω)) := by
  simpa using (Fintype.card_pos_iff.mpr ⟨⟨ω, rfl⟩⟩)

/-- Paper label: `prop:op-algebra-dmax-capacity-equals-log-index`.
In the finite fold model, every point-mass loss is bounded by the logarithm of the largest fiber,
and the exact supremum is attained there. -/
theorem paper_op_algebra_dmax_capacity_equals_log_index (fold : Ω → X)
    (hfold : Function.Surjective fold) :
    (∀ ω, foldFiberRenyiFlatness fold ω ≤ Real.log (foldLargestFiberCard fold)) ∧
      foldDmaxCapacity fold = Real.log (foldLargestFiberCard fold) := by
  have hcap : ∀ ω, Fintype.card (foldFiber fold (fold ω)) ≤ foldLargestFiberCard fold := by
    intro ω
    exact Finset.le_sup (f := fun x : X => Fintype.card (foldFiber fold x)) (Finset.mem_univ _)
  have hsup :
      sSup (Set.range (foldFiberRenyiFlatness fold)) = Real.log (foldLargestFiberCard fold) :=
    (paper_op_algebra_index_extremal_entropy_loss_maxfiber fold hfold).2.2.1
  refine ⟨?_, ?_⟩
  · intro ω
    unfold foldFiberRenyiFlatness
    have hωpos : 0 < (Fintype.card (foldFiber fold (fold ω)) : ℝ) := by
      exact_mod_cast foldFiber_card_pos_at_point fold ω
    exact Real.log_le_log hωpos (by exact_mod_cast hcap ω)
  · simpa [foldDmaxCapacity] using hsup

end

end Omega.OperatorAlgebra
