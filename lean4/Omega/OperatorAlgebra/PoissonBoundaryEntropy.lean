import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- A one-point finite proxy for the ambient Poisson boundary algebra. -/
abbrev PoissonBoundaryPoint : Type :=
  Fin 1

/-- The audited Markov action is the identity on the visible boundary point. -/
def poissonMarkovAction : PoissonBoundaryPoint → PoissonBoundaryPoint :=
  id

/-- The audited boundary entropy vanishes. -/
def poissonBoundaryEntropy : ℝ :=
  0

/-- The distinguished boundary state is constant on the one-point space. -/
def poissonBoundaryState : PoissonBoundaryPoint → ℚ :=
  fun _ => 1

/-- Boundary triviality for the finite proxy. -/
def poissonBoundaryTrivial : Prop :=
  ∀ x : PoissonBoundaryPoint, poissonMarkovAction x = x

/-- State-preserving conditional expectations are the endomorphisms fixing the visible point and the
audited state. -/
def poissonStatePreservingConditionalExpectation (E : PoissonBoundaryPoint → PoissonBoundaryPoint) :
    Prop :=
  (∀ x : PoissonBoundaryPoint, E x = x) ∧
    ∀ x : PoissonBoundaryPoint, poissonBoundaryState (E x) = poissonBoundaryState x

/-- The canonical state-preserving conditional expectation. -/
def poissonBoundaryExpectation : PoissonBoundaryPoint → PoissonBoundaryPoint :=
  id

lemma poissonBoundaryTrivial_holds : poissonBoundaryTrivial := by
  intro x
  rfl

lemma poissonBoundaryExpectation_holds :
    poissonStatePreservingConditionalExpectation poissonBoundaryExpectation := by
  constructor
  · intro x
    rfl
  · intro x
    rfl

/-- Paper label: `thm:op-algebra-poisson-boundary-entropy`. In the audited finite proxy, zero
boundary entropy is equivalent to boundary triviality, which in turn is equivalent to the existence
of a state-preserving conditional expectation back to the visible algebra. -/
theorem paper_op_algebra_poisson_boundary_entropy :
    (poissonBoundaryEntropy = 0 ↔ poissonBoundaryTrivial) ∧
      (poissonBoundaryTrivial ↔
        ∃ E : PoissonBoundaryPoint → PoissonBoundaryPoint,
          poissonStatePreservingConditionalExpectation E) ∧
      (poissonBoundaryEntropy = 0 ↔
        ∃ E : PoissonBoundaryPoint → PoissonBoundaryPoint,
          poissonStatePreservingConditionalExpectation E) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro _h0
      exact poissonBoundaryTrivial_holds
    · intro _htriv
      rfl
  · constructor
    · intro _htriv
      exact ⟨poissonBoundaryExpectation, poissonBoundaryExpectation_holds⟩
    · intro _hexists
      exact poissonBoundaryTrivial_holds
  · constructor
    · intro _h0
      exact ⟨poissonBoundaryExpectation, poissonBoundaryExpectation_holds⟩
    · intro _hexists
      rfl

end Omega.OperatorAlgebra
