import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Omega.Folding.OracleCapacityClosedForm
import Omega.OperatorAlgebra.FoldWatataniIndexMultiplicityField

namespace Omega.Folding

open scoped BigOperators

/-- The truncated Watatani index coefficient on the `x`-block. -/
def fold_oracle_watatani_index_trace_formula_truncated_index {Ω X : Type*} [Fintype Ω]
    [Fintype X] [DecidableEq Ω] [DecidableEq X] (fold : Ω → X) (B : Nat) (x : X) : Nat :=
  Nat.min (Omega.OperatorAlgebra.foldWatataniIndexElement fold x) (2 ^ B)

/-- The finite commutative trace of the truncated Watatani index field. -/
def fold_oracle_watatani_index_trace_formula_truncated_trace {Ω X : Type*} [Fintype Ω]
    [Fintype X] [DecidableEq Ω] [DecidableEq X] (fold : Ω → X) (B : Nat) : Nat :=
  ∑ x : X, fold_oracle_watatani_index_trace_formula_truncated_index fold B x

/-- Paper-facing trace formula equating the `B`-bit oracle capacity with the truncated Watatani
index trace. -/
def fold_oracle_watatani_index_trace_formula_statement {Ω X : Type*} [Fintype Ω]
    [Fintype X] [DecidableEq Ω] [DecidableEq X] (fold : Ω → X) (B : Nat) : Prop :=
  Omega.POM.bbitOracleCapacity fold B =
    fold_oracle_watatani_index_trace_formula_truncated_trace fold B

theorem paper_fold_oracle_watatani_index_trace_formula {Ω X : Type*} [Fintype Ω]
    [Fintype X] [DecidableEq Ω] [DecidableEq X] (fold : Ω -> X) (B : Nat) :
    fold_oracle_watatani_index_trace_formula_statement fold B := by
  simpa [fold_oracle_watatani_index_trace_formula_statement,
    fold_oracle_watatani_index_trace_formula_truncated_trace,
    fold_oracle_watatani_index_trace_formula_truncated_index,
    Omega.OperatorAlgebra.foldWatataniIndexElement,
    Omega.OperatorAlgebra.foldWatataniIndexCoefficient] using
    paper_fold_oracle_capacity_closed_form fold B

end Omega.Folding
