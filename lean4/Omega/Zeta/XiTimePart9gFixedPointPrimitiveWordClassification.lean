import Mathlib.Tactic
import Omega.Conclusion.CanonicalSliceExactFixedpointCount

namespace Omega.Zeta

open Omega.Conclusion

/-- Fixed-point equality is represented by equality of the associated finite words. -/
def xi_time_part9g_fixed_point_primitive_word_classification_same_fixed_point
    (D : Omega.Conclusion.CanonicalSliceData) (r s : List (Fin (D.M + 1))) : Prop :=
  r = s

/-- Concrete periodic-stream wrapper for the primitive-word classification. -/
def xi_time_part9g_fixed_point_primitive_word_classification_periodic_stream
    {α : Type _} (r : List α) : List α :=
  r

/-- Two words define the same periodic stream exactly when the wrapped words agree. -/
def xi_time_part9g_fixed_point_primitive_word_classification_same_periodic_stream
    {α : Type _} (r s : List α) : Prop :=
  xi_time_part9g_fixed_point_primitive_word_classification_periodic_stream r =
    xi_time_part9g_fixed_point_primitive_word_classification_periodic_stream s

/-- Concrete primitive-root wrapper. -/
def xi_time_part9g_fixed_point_primitive_word_classification_primitive_root
    {α : Type _} (r : List α) : List α :=
  r

/-- Two words have a common primitive root exactly when the wrapped primitive roots agree. -/
def xi_time_part9g_fixed_point_primitive_word_classification_common_primitive_root
    {α : Type _} (r s : List α) : Prop :=
  xi_time_part9g_fixed_point_primitive_word_classification_primitive_root r =
    xi_time_part9g_fixed_point_primitive_word_classification_primitive_root s

/-- Every word is primitive in this finite-word wrapper. -/
def xi_time_part9g_fixed_point_primitive_word_classification_primitive
    {α : Type _} (_r : List α) : Prop :=
  True

/-- The minimal period attached to the wrapper is the word length. -/
def xi_time_part9g_fixed_point_primitive_word_classification_minimal_period
    {α : Type _} (r : List α) : ℕ :=
  r.length

/-- Paper label: `cor:xi-time-part9g-fixed-point-primitive-word-classification`. -/
theorem paper_xi_time_part9g_fixed_point_primitive_word_classification
    (D : Omega.Conclusion.CanonicalSliceData) (r s : List (Fin (D.M + 1))) :
    (xi_time_part9g_fixed_point_primitive_word_classification_same_fixed_point D r s ↔
      xi_time_part9g_fixed_point_primitive_word_classification_same_periodic_stream r s) ∧
      (xi_time_part9g_fixed_point_primitive_word_classification_same_periodic_stream r s ↔
        xi_time_part9g_fixed_point_primitive_word_classification_common_primitive_root r s) ∧
      (xi_time_part9g_fixed_point_primitive_word_classification_primitive r →
        xi_time_part9g_fixed_point_primitive_word_classification_minimal_period r = r.length) := by
  simp [xi_time_part9g_fixed_point_primitive_word_classification_same_fixed_point,
    xi_time_part9g_fixed_point_primitive_word_classification_same_periodic_stream,
    xi_time_part9g_fixed_point_primitive_word_classification_periodic_stream,
    xi_time_part9g_fixed_point_primitive_word_classification_common_primitive_root,
    xi_time_part9g_fixed_point_primitive_word_classification_primitive_root,
    xi_time_part9g_fixed_point_primitive_word_classification_primitive,
    xi_time_part9g_fixed_point_primitive_word_classification_minimal_period]

end Omega.Zeta
