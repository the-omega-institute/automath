import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.Conclusion.FibadicPrimitiveCentralIdempotents

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite active-depth coordinate data for the semisimple model. -/
structure conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_data where
  ActiveDepth : Type
  activeDepthFintype : Fintype ActiveDepth
  activeDepthDecidableEq : DecidableEq ActiveDepth

attribute [instance]
  conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_data.activeDepthFintype
  conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_data.activeDepthDecidableEq

/-- Coordinate functions on the active-depth set. -/
abbrev conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_algebra
    (D : conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_data) :=
  D.ActiveDepth → ℚ

/-- The primitive coordinate idempotent attached to one active depth. -/
def conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_primitive
    (D : conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_data)
    (d : D.ActiveDepth) :
    conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_algebra D :=
  fun e => if e = d then 1 else 0

/-- Predicate saying that a coordinate is one of the visible primitive depth idempotents. -/
def conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_isPrimitive
    (D : conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_data)
    (p : conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_algebra D) :
    Prop :=
  ∃ d, p =
    conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_primitive D d

/-- Paper-facing finite coordinate statement: idempotents in the coordinate algebra are exactly
indicator functions of subsets, and each active depth contributes its primitive coordinate. -/
def conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_data.Holds
    (D : conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_data) :
    Prop :=
  (∀ e : conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_algebra D,
    (∀ d, e d * e d = e d) →
      ∃ S : Finset D.ActiveDepth, ∀ d, e d = if d ∈ S then 1 else 0) ∧
    (∀ d,
      conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_isPrimitive D
        (conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_primitive D
          d)) ∧
      ∀ d e,
        conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_primitive D d
            e =
          if e = d then 1 else 0

/-- Paper label:
`cor:conclusion-fibadic-finite-layer-conditional-expectation-semisimple-coordinates`. -/
theorem paper_conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates
    (D :
      conclusion_fibadic_finite_layer_conditional_expectation_semisimple_coordinates_data) :
    D.Holds := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    exact _root_.Omega.Conclusion.FibadicPrimitiveCentralIdempotents.paper_conclusion_fibadic_primitive_central_idempotents_package e he
  · intro d
    exact ⟨d, rfl⟩
  · intro d e
    rfl

end Omega.Conclusion
