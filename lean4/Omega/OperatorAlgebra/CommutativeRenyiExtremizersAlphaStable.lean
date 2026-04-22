import Omega.OperatorAlgebra.CommutativeDmaxExtremizersMaxfiber
import Omega.OperatorAlgebra.FoldDmaxCapacityEqualsLogIndex
import Omega.OperatorAlgebra.RenyiLossSpectrumCappedByIndex

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] [Fintype X] [DecidableEq X]

/-- Paper label: `cor:op-algebra-commutative-renyi-extremizers-alpha-stable`.
In the finite commutative fold model, the extremizing point masses are exactly those supported on
maximal fibers; hence the extremizer set is stable across the Rényi family once it is identified at
the `Dmax` endpoint. -/
def op_algebra_commutative_renyi_extremizers_alpha_stable_statement (fold : Ω → X) : Prop :=
  foldDmaxCapacity fold = Real.log (foldLargestFiberCard fold) ∧
    (∀ ω, foldFiberRenyiFlatness fold ω ≤ foldDmaxCapacity fold) ∧
    (∀ ω, foldFiberRenyiFlatness fold ω = foldDmaxCapacity fold ↔
      Fintype.card (foldFiber fold (fold ω)) = foldLargestFiberCard fold) ∧
    ∃ ω, foldFiberRenyiFlatness fold ω = foldDmaxCapacity fold

theorem paper_op_algebra_commutative_renyi_extremizers_alpha_stable {Ω X : Type*} [Fintype Ω]
    [DecidableEq Ω] [Nonempty Ω] [Fintype X] [DecidableEq X] (fold : Ω → X)
    (hfold : Function.Surjective fold) :
    op_algebra_commutative_renyi_extremizers_alpha_stable_statement fold := by
  exact paper_op_algebra_commutative_dmax_extremizers_maxfiber fold hfold

end

end Omega.OperatorAlgebra
