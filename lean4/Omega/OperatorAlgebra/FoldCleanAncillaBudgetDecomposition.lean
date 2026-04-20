import Omega.OperatorAlgebra.FoldCleanAncillaReversibleDilation

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- Fiber potential appearing in the clean-ancilla budget decomposition. -/
noncomputable def foldFiberPotential {Ω X : Type} [Fintype Ω] [DecidableEq Ω] [Fintype X]
    [DecidableEq X] (Fold : Ω → X) (f : X → X) (y : X) : ℕ :=
  ∑ x : X, if f x = y then fiberMultiplicity Fold x else 0

/-- Chapter-local budget decomposition wrapper for clean-ancilla dilation. -/
def FoldCleanAncillaBudgetDecomposition {Ω X : Type} [Fintype Ω] [DecidableEq Ω] [Fintype X]
    [DecidableEq X] (Fold : Ω → X) (f : X → X) : Prop :=
  ∀ B : ℕ, CleanAncillaReversibleRealizable Fold f B ↔
    ∀ y : X, foldFiberPotential Fold f y ≤ fiberMultiplicity Fold y * 2 ^ B

/-- Paper: `cor:op-algebra-fold-clean-ancilla-budget-decomposition`. -/
theorem paper_op_algebra_fold_clean_ancilla_budget_decomposition {Ω X : Type} [Fintype Ω]
    [DecidableEq Ω] [Fintype X] [DecidableEq X] (Fold : Ω → X) (f : X → X) :
    FoldCleanAncillaBudgetDecomposition Fold f := by
  intro B
  constructor
  · intro h y
    simpa [foldFiberPotential, weightedIndegree] using h y
  · intro h
    exact (paper_op_algebra_fold_clean_ancilla_reversible_dilation Fold f B).2 <| by
      intro y
      simpa [foldFiberPotential, weightedIndegree] using h y

end Omega.OperatorAlgebra
