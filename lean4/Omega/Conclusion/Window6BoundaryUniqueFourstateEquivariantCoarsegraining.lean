import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryC3DiagonalIrreducibleSplitting
import Omega.Conclusion.Window6BoundaryTwoResidualBitsNongeometricNonrational

namespace Omega.Conclusion

/-- The four quotient states of the diagonal boundary character quotient. -/
abbrev conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_state :=
  ZMod 2 × ZMod 2

/-- Quotient map by the diagonal character line. -/
def conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_quotient
    (x : BoundaryParityVector) :
    conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_state :=
  (x 0 + x 2, x 1 + x 2)

/-- The induced cyclic action on the four quotient states. -/
def conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_c3_action
    (s : conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_state) :
    conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_state :=
  (s.1 + s.2, s.1)

/-- The quotient has exactly four states. -/
def conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_fourstate : Prop :=
  Fintype.card
      conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_state = 4

/-- The concrete quotient predicate: it is surjective and identifies exactly the diagonal line. -/
def conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_quotient_predicate :
    Prop :=
  Function.Surjective
      conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_quotient ∧
    ∀ x y : BoundaryParityVector,
      conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_quotient x =
          conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_quotient y ↔
        x + y = 0 ∨ x + y = boundaryDiagonal

/-- The quotient is equivariant for the boundary `C₃` rotation and the induced four-state action. -/
def conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_equivariant :
    Prop :=
  ∀ x : BoundaryParityVector,
    conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_quotient
        (boundaryRotate x) =
      conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_c3_action
        (conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_quotient x)

/-- The concrete quotient is the canonical four-state `C₃` module model. -/
def conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_isomorphism_predicate :
    Prop :=
  ∀ s : conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_state,
    ∃ x : BoundaryParityVector,
      conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_quotient x = s ∧
        conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_quotient
            (boundaryRotate x) =
          conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_c3_action s

/-- Concrete package for the unique four-state equivariant coarsegraining. -/
def conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_statement : Prop :=
  BoundaryParityC3DiagonalIrreducibleSplittingLaw ∧
    conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_fourstate ∧
    conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_quotient_predicate ∧
    conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_equivariant ∧
    conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_isomorphism_predicate

/-- Paper label:
`thm:conclusion-window6-boundary-unique-fourstate-equivariant-coarsegraining`. -/
theorem paper_conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining :
    conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_statement := by
  unfold conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_statement
  refine ⟨paper_conclusion_window6_boundary_c3_diagonal_irreducible_splitting, ?_, ?_, ?_, ?_⟩
  · unfold conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_fourstate
    native_decide
  · unfold conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_quotient_predicate
    native_decide
  · unfold conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_equivariant
    native_decide
  · unfold
      conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_isomorphism_predicate
    intro s
    refine ⟨![s.1, s.2, 0], ?_, ?_⟩
    · simp [conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_quotient]
    · have h :=
        (show conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_equivariant by
          unfold conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_equivariant
          native_decide)
      simpa [conclusion_window6_boundary_unique_fourstate_equivariant_coarsegraining_quotient] using
        h ![s.1, s.2, 0]

end Omega.Conclusion
