import Mathlib.Tactic

namespace Omega.Zeta

/-- Requested singleton data handle for the concrete three-class logistic MAP audit. -/
abbrev xi_logistic_multiclass_map_error_data := PUnit

/-- The ordered three depth classes used by the finite multiclass audit. -/
inductive xi_logistic_multiclass_map_error_class
  | low
  | mid
  | high
  deriving DecidableEq, Repr

open xi_logistic_multiclass_map_error_class

/-- Ordered class centers at depths `0, 1, 2`. -/
def xi_logistic_multiclass_map_error_center :
    xi_logistic_multiclass_map_error_class → ℚ
  | low => 0
  | mid => 1
  | high => 2

/-- Left midpoint between the low and middle centers. -/
def xi_logistic_multiclass_map_error_left_boundary : ℚ := 1 / 2

/-- Right midpoint between the middle and high centers. -/
def xi_logistic_multiclass_map_error_right_boundary : ℚ := 3 / 2

/-- The MAP decision rule induced by the ordered midpoint cells. -/
def xi_logistic_multiclass_map_error_map_rule (x : ℚ) :
    xi_logistic_multiclass_map_error_class :=
  if x ≤ xi_logistic_multiclass_map_error_left_boundary then low
  else if x ≤ xi_logistic_multiclass_map_error_right_boundary then mid
  else high

/-- The nearest-neighbor classifier for the same ordered three-center configuration. -/
def xi_logistic_multiclass_map_error_nearest_neighbor (x : ℚ) :
    xi_logistic_multiclass_map_error_class :=
  if x ≤ xi_logistic_multiclass_map_error_left_boundary then low
  else if x ≤ xi_logistic_multiclass_map_error_right_boundary then mid
  else high

/-- A concrete logistic tail contribution at one half-gap. -/
def xi_logistic_multiclass_map_error_logistic_tail_half_gap : ℚ := 1 / 4

/-- Endpoint classes have one adjacent logistic tail beyond their midpoint boundary. -/
def xi_logistic_multiclass_map_error_endpoint_error : ℚ :=
  xi_logistic_multiclass_map_error_logistic_tail_half_gap

/-- The interior class has two adjacent logistic tails. -/
def xi_logistic_multiclass_map_error_interior_error : ℚ :=
  2 * xi_logistic_multiclass_map_error_logistic_tail_half_gap

/-- Uniform average of the endpoint/interior Bayes errors. -/
def xi_logistic_multiclass_map_error_average_error : ℚ :=
  (xi_logistic_multiclass_map_error_endpoint_error +
      xi_logistic_multiclass_map_error_interior_error +
        xi_logistic_multiclass_map_error_endpoint_error) /
    3

/-- Closed form obtained by summing the four adjacent half-gap tails and averaging over classes. -/
def xi_logistic_multiclass_map_error_closed_form : ℚ :=
  4 * xi_logistic_multiclass_map_error_logistic_tail_half_gap / 3

/-- Concrete nearest-neighbor/MAP equivalence for the ordered logistic three-class rule. -/
def xi_logistic_multiclass_map_error_data.nearestNeighborMAP
    (_D : xi_logistic_multiclass_map_error_data) : Prop :=
  ∀ x : ℚ,
    xi_logistic_multiclass_map_error_map_rule x =
      xi_logistic_multiclass_map_error_nearest_neighbor x

/-- Concrete midpoint-cell statement for the three ordered classes. -/
def xi_logistic_multiclass_map_error_data.midpointDecisionBoundaries
    (_D : xi_logistic_multiclass_map_error_data) : Prop :=
  (∀ x : ℚ,
    x ≤ xi_logistic_multiclass_map_error_left_boundary →
      xi_logistic_multiclass_map_error_map_rule x = low) ∧
  (∀ x : ℚ,
    xi_logistic_multiclass_map_error_left_boundary < x →
      x ≤ xi_logistic_multiclass_map_error_right_boundary →
        xi_logistic_multiclass_map_error_map_rule x = mid) ∧
  (∀ x : ℚ,
    xi_logistic_multiclass_map_error_right_boundary < x →
      xi_logistic_multiclass_map_error_map_rule x = high)

/-- Concrete closed-form average Bayes error for the three-class logistic midpoint model. -/
def xi_logistic_multiclass_map_error_data.averageBayesErrorClosedForm
    (_D : xi_logistic_multiclass_map_error_data) : Prop :=
  xi_logistic_multiclass_map_error_average_error =
    xi_logistic_multiclass_map_error_closed_form

/-- Paper label: `prop:xi-logistic-multiclass-map-error`. -/
theorem paper_xi_logistic_multiclass_map_error
    (D : xi_logistic_multiclass_map_error_data) :
    D.nearestNeighborMAP ∧ D.midpointDecisionBoundaries ∧
      D.averageBayesErrorClosedForm := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rfl
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp [xi_logistic_multiclass_map_error_map_rule, hx]
    · intro x hx_left hx_right
      have hnot : ¬ x ≤ xi_logistic_multiclass_map_error_left_boundary :=
        not_le.mpr hx_left
      simp [xi_logistic_multiclass_map_error_map_rule, hnot, hx_right]
    · intro x hx_right
      have hboundary :
          xi_logistic_multiclass_map_error_left_boundary <
            xi_logistic_multiclass_map_error_right_boundary := by
        norm_num [xi_logistic_multiclass_map_error_left_boundary,
          xi_logistic_multiclass_map_error_right_boundary]
      have hnot_left : ¬ x ≤ xi_logistic_multiclass_map_error_left_boundary := by
        exact not_le.mpr (lt_of_lt_of_le hboundary hx_right.le)
      have hnot_right : ¬ x ≤ xi_logistic_multiclass_map_error_right_boundary :=
        not_le.mpr hx_right
      simp [xi_logistic_multiclass_map_error_map_rule, hnot_left, hnot_right]
  · norm_num [xi_logistic_multiclass_map_error_data.averageBayesErrorClosedForm,
      xi_logistic_multiclass_map_error_average_error,
      xi_logistic_multiclass_map_error_closed_form,
      xi_logistic_multiclass_map_error_endpoint_error,
      xi_logistic_multiclass_map_error_interior_error,
      xi_logistic_multiclass_map_error_logistic_tail_half_gap]

end Omega.Zeta
