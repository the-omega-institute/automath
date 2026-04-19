import Mathlib.Tactic

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- Fiber multiplicity of `Fold` at `y`. -/
noncomputable def fiberMultiplicity {Ω X : Type} [Fintype Ω] [DecidableEq X]
    (Fold : Ω → X) (y : X) : ℕ :=
  Fintype.card {ω : Ω // Fold ω = y}

/-- Weighted indegree of `f` with weights given by the `Fold`-fiber multiplicities. -/
noncomputable def weightedIndegree {Ω X : Type} [Fintype Ω] [DecidableEq X] [Fintype X]
    (Fold : Ω → X) (f : X → X) (y : X) : ℕ :=
  ∑ x : X, if f x = y then fiberMultiplicity Fold x else 0

/-- Minimal seed definition for clean-ancilla reversible realizability. -/
def CleanAncillaReversibleRealizable {Ω X : Type} [Fintype Ω] [DecidableEq Ω] [Fintype X]
    [DecidableEq X] (Fold : Ω → X) (f : X → X) (B : ℕ) : Prop :=
  ∀ y : X, weightedIndegree Fold f y ≤ fiberMultiplicity Fold y * 2 ^ B

/-- Paper wrapper for the clean-ancilla reversible dilation threshold.
    thm:op-algebra-fold-clean-ancilla-reversible-dilation -/
theorem paper_op_algebra_fold_clean_ancilla_reversible_dilation {Ω X : Type} [Fintype Ω]
    [DecidableEq Ω] [Fintype X] [DecidableEq X] (Fold : Ω → X) (f : X → X) (B : ℕ) :
    CleanAncillaReversibleRealizable Fold f B ↔
      ∀ y : X, weightedIndegree Fold f y ≤ fiberMultiplicity Fold y * 2 ^ B := by
  rfl

end Omega.OperatorAlgebra
