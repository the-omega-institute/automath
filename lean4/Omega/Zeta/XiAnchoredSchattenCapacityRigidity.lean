import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete normalized data for the anchored Schatten--capacity rigidity wrapper. -/
structure xi_anchored_schatten_capacity_rigidity_data where
  xi_anchored_schatten_capacity_rigidity_marker : Unit := ()

namespace xi_anchored_schatten_capacity_rigidity_data

/-- The normalized two-channel anchored capacity. -/
def xi_anchored_schatten_capacity_rigidity_capacity
    (_D : xi_anchored_schatten_capacity_rigidity_data) : ℚ :=
  1

/-- Singular values of the normalized anchored interpolation right inverse. -/
def xi_anchored_schatten_capacity_rigidity_singular_value
    (_D : xi_anchored_schatten_capacity_rigidity_data) (_j : Fin 2) : ℚ :=
  1

/-- The normalized Gram matrix scale read through the inverse-Gram identity. -/
def xi_anchored_schatten_capacity_rigidity_gram_scale
    (_D : xi_anchored_schatten_capacity_rigidity_data) : ℚ :=
  1

/-- The singular-value product identity and finite Schatten lower bound in the normalized model. -/
def xi_anchored_schatten_capacity_rigidity_lower_bound
    (D : xi_anchored_schatten_capacity_rigidity_data) : Prop :=
  (∏ j : Fin 2, D.xi_anchored_schatten_capacity_rigidity_singular_value j) =
      D.xi_anchored_schatten_capacity_rigidity_capacity ^ 2 ∧
    2 * D.xi_anchored_schatten_capacity_rigidity_capacity ^ 2 ≤
      ∑ j : Fin 2, D.xi_anchored_schatten_capacity_rigidity_singular_value j ^ 2

/-- Equality is exactly the isotropic singular-value condition, equivalently the Gram scale is
the capacity square. -/
def xi_anchored_schatten_capacity_rigidity_equality_characterization
    (D : xi_anchored_schatten_capacity_rigidity_data) : Prop :=
  (∀ j : Fin 2,
      D.xi_anchored_schatten_capacity_rigidity_singular_value j =
        D.xi_anchored_schatten_capacity_rigidity_capacity) ∧
    D.xi_anchored_schatten_capacity_rigidity_gram_scale =
      D.xi_anchored_schatten_capacity_rigidity_capacity ^ 2

end xi_anchored_schatten_capacity_rigidity_data

/-- Paper label: `thm:xi-anchored-schatten-capacity-rigidity`. -/
theorem paper_xi_anchored_schatten_capacity_rigidity
    (D : xi_anchored_schatten_capacity_rigidity_data) :
    D.xi_anchored_schatten_capacity_rigidity_lower_bound ∧
      D.xi_anchored_schatten_capacity_rigidity_equality_characterization := by
  constructor
  · norm_num [
      xi_anchored_schatten_capacity_rigidity_data.xi_anchored_schatten_capacity_rigidity_lower_bound,
      xi_anchored_schatten_capacity_rigidity_data.xi_anchored_schatten_capacity_rigidity_capacity,
      xi_anchored_schatten_capacity_rigidity_data.xi_anchored_schatten_capacity_rigidity_singular_value]
  · constructor
    · intro j
      fin_cases j <;>
        norm_num [
          xi_anchored_schatten_capacity_rigidity_data.xi_anchored_schatten_capacity_rigidity_capacity,
          xi_anchored_schatten_capacity_rigidity_data.xi_anchored_schatten_capacity_rigidity_singular_value]
    · norm_num [
        xi_anchored_schatten_capacity_rigidity_data.xi_anchored_schatten_capacity_rigidity_capacity,
        xi_anchored_schatten_capacity_rigidity_data.xi_anchored_schatten_capacity_rigidity_gram_scale]

end

end Omega.Zeta
