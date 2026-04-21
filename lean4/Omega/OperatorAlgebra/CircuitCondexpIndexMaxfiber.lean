import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldConditionalExpectation
import Omega.OperatorAlgebra.FoldIndexExtremalEntropyLossMaxfiber

namespace Omega.OperatorAlgebra

/-- Concrete finite circuit coarse-graining data for the conditional-expectation / maxfiber
comparison. -/
structure CircuitCondexpIndexMaxfiberData where
  Ω : Type
  X : Type
  instDecEqΩ : DecidableEq Ω
  instFintypeΩ : Fintype Ω
  instNonemptyΩ : Nonempty Ω
  instDecEqX : DecidableEq X
  instFintypeX : Fintype X
  circuit : Ω → X
  circuit_surjective : Function.Surjective circuit

attribute [instance] CircuitCondexpIndexMaxfiberData.instDecEqΩ
attribute [instance] CircuitCondexpIndexMaxfiberData.instFintypeΩ
attribute [instance] CircuitCondexpIndexMaxfiberData.instNonemptyΩ
attribute [instance] CircuitCondexpIndexMaxfiberData.instDecEqX
attribute [instance] CircuitCondexpIndexMaxfiberData.instFintypeX

namespace CircuitCondexpIndexMaxfiberData

/-- The circuit map induces the standard finite fold conditional expectation. -/
def toFoldConditionalExpectationData (D : CircuitCondexpIndexMaxfiberData) :
    FoldConditionalExpectationData where
  Ω := D.Ω
  X := D.X
  instDecEqΩ := D.instDecEqΩ
  instFintypeΩ := D.instFintypeΩ
  instDecEqX := D.instDecEqX
  instFintypeX := D.instFintypeX
  fold := D.circuit
  fold_surjective := D.circuit_surjective

/-- The Pimsner-Popa / Watatani index of the circuit conditional expectation equals the maximal
fiber multiplicity. -/
def IndexEqualsMaxfiber (D : CircuitCondexpIndexMaxfiberData) : Prop :=
  foldIndexEqualsMaxFiber D.circuit

/-- The extremal relative-entropy loss is the logarithm of the largest circuit fiber. -/
def MaxRelativeEntropyLossEqualsLogMaxfiber (D : CircuitCondexpIndexMaxfiberData) : Prop :=
  sSup (Set.range (foldFiberRenyiFlatness D.circuit)) = Real.log (foldLargestFiberCard D.circuit)

end CircuitCondexpIndexMaxfiberData

open CircuitCondexpIndexMaxfiberData

/-- Paper label: `prop:circuit-condexp-index-maxfiber`. Specializing the finite fold
conditional-expectation package to the circuit map identifies the index with the maximal fiber and
the maximal relative-entropy loss with its logarithm. -/
theorem paper_circuit_condexp_index_maxfiber (D : CircuitCondexpIndexMaxfiberData) :
    D.IndexEqualsMaxfiber ∧ D.MaxRelativeEntropyLossEqualsLogMaxfiber := by
  have _ := paper_op_algebra_fold_conditional_expectation D.toFoldConditionalExpectationData
  rcases paper_op_algebra_index_extremal_entropy_loss_maxfiber D.circuit D.circuit_surjective with
    ⟨hIndex, _, hLoss⟩
  exact ⟨hIndex, hLoss.1⟩

end Omega.OperatorAlgebra
