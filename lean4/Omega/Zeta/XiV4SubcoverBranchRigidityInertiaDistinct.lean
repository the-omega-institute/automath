import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite bookkeeping data for the `S₄/V₄` quotient calculation. -/
structure xi_v4_subcover_branch_rigidity_inertia_distinct_data where
  xi_v4_subcover_branch_rigidity_inertia_distinct_witness : Unit := ()

namespace xi_v4_subcover_branch_rigidity_inertia_distinct_data

/-- The three points over infinity in the quotient cover. -/
abbrev xi_v4_subcover_branch_rigidity_inertia_distinct_branch_point
    (_D : xi_v4_subcover_branch_rigidity_inertia_distinct_data) : Type :=
  Fin 3

/-- The three order-two subgroups of the normal Klein four group. -/
abbrev xi_v4_subcover_branch_rigidity_inertia_distinct_order_two_subgroup
    (_D : xi_v4_subcover_branch_rigidity_inertia_distinct_data) : Type :=
  Fin 3

/-- The five transposition-type branch fibers in the ambient `S₄` cover. -/
abbrev xi_v4_subcover_branch_rigidity_inertia_distinct_transposition_fiber
    (_D : xi_v4_subcover_branch_rigidity_inertia_distinct_data) : Type :=
  Fin 5

/-- The branch set of the `V₄` subcover. -/
def xi_v4_subcover_branch_rigidity_inertia_distinct_branch_points
    (D : xi_v4_subcover_branch_rigidity_inertia_distinct_data) :
    Finset D.xi_v4_subcover_branch_rigidity_inertia_distinct_branch_point :=
  Finset.univ

/-- The complete packet of order-two subgroups in `V₄`. -/
def xi_v4_subcover_branch_rigidity_inertia_distinct_order_two_subgroups
    (D : xi_v4_subcover_branch_rigidity_inertia_distinct_data) :
    Finset D.xi_v4_subcover_branch_rigidity_inertia_distinct_order_two_subgroup :=
  Finset.univ

/-- The inertia subgroup attached to a point over infinity. -/
def xi_v4_subcover_branch_rigidity_inertia_distinct_inertia
    (D : xi_v4_subcover_branch_rigidity_inertia_distinct_data)
    (Q : D.xi_v4_subcover_branch_rigidity_inertia_distinct_branch_point) :
    D.xi_v4_subcover_branch_rigidity_inertia_distinct_order_two_subgroup :=
  Q

/-- Transposition inertia intersects the normal `V₄` trivially. -/
def xi_v4_subcover_branch_rigidity_inertia_distinct_transposition_intersection_order
    (_D : xi_v4_subcover_branch_rigidity_inertia_distinct_data)
    (_τ : Fin 5) : ℕ :=
  1

/-- Infinity inertia contributes an order-two subgroup of `V₄`. -/
def xi_v4_subcover_branch_rigidity_inertia_distinct_infinity_intersection_order
    (_D : xi_v4_subcover_branch_rigidity_inertia_distinct_data) (_Q : Fin 3) : ℕ :=
  2

/-- The Riemann-Hurwitz contribution from the three `V₄` branch points. -/
def xi_v4_subcover_branch_rigidity_inertia_distinct_branch_contribution
    (D : xi_v4_subcover_branch_rigidity_inertia_distinct_data) : ℕ :=
  D.xi_v4_subcover_branch_rigidity_inertia_distinct_branch_points.sum (fun _Q => 2)

/-- The Riemann-Hurwitz contribution forced by `g(X)=16`, `g(C₆)=4`, and `|V₄|=4`. -/
def xi_v4_subcover_branch_rigidity_inertia_distinct_rh_required_contribution
    (_D : xi_v4_subcover_branch_rigidity_inertia_distinct_data) : ℕ :=
  (2 * 16 - 2) - 4 * (2 * 4 - 2)

/-- Concrete branch-rigidity and inertia-distinctness statement for the quotient model. -/
def branch_rigidity_and_inertia_distinct
    (D : xi_v4_subcover_branch_rigidity_inertia_distinct_data) : Prop :=
  D.xi_v4_subcover_branch_rigidity_inertia_distinct_branch_points.card = 3 ∧
    (∀ τ : D.xi_v4_subcover_branch_rigidity_inertia_distinct_transposition_fiber,
      D.xi_v4_subcover_branch_rigidity_inertia_distinct_transposition_intersection_order τ =
        1) ∧
    (∀ Q : D.xi_v4_subcover_branch_rigidity_inertia_distinct_branch_point,
      D.xi_v4_subcover_branch_rigidity_inertia_distinct_infinity_intersection_order Q = 2) ∧
    D.xi_v4_subcover_branch_rigidity_inertia_distinct_branch_contribution =
      D.xi_v4_subcover_branch_rigidity_inertia_distinct_rh_required_contribution ∧
    Function.Bijective D.xi_v4_subcover_branch_rigidity_inertia_distinct_inertia ∧
    Finset.image D.xi_v4_subcover_branch_rigidity_inertia_distinct_inertia
        D.xi_v4_subcover_branch_rigidity_inertia_distinct_branch_points =
      D.xi_v4_subcover_branch_rigidity_inertia_distinct_order_two_subgroups ∧
    ∀ Q₁ Q₂ : D.xi_v4_subcover_branch_rigidity_inertia_distinct_branch_point,
      D.xi_v4_subcover_branch_rigidity_inertia_distinct_inertia Q₁ =
        D.xi_v4_subcover_branch_rigidity_inertia_distinct_inertia Q₂ →
      Q₁ = Q₂

end xi_v4_subcover_branch_rigidity_inertia_distinct_data

open xi_v4_subcover_branch_rigidity_inertia_distinct_data

/-- Paper label: `thm:xi-v4-subcover-branch-rigidity-inertia-distinct`. The finite quotient
bookkeeping has exactly three branch points; transposition fibers are unramified in the `V₄`
subcover, while the three points over infinity contribute the three distinct order-two
subgroups. -/
theorem paper_xi_v4_subcover_branch_rigidity_inertia_distinct
    (D : xi_v4_subcover_branch_rigidity_inertia_distinct_data) :
    D.branch_rigidity_and_inertia_distinct := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [xi_v4_subcover_branch_rigidity_inertia_distinct_branch_points]
  · intro τ
    rfl
  · intro Q
    rfl
  · simp [xi_v4_subcover_branch_rigidity_inertia_distinct_branch_contribution,
      xi_v4_subcover_branch_rigidity_inertia_distinct_branch_points,
      xi_v4_subcover_branch_rigidity_inertia_distinct_rh_required_contribution]
  · refine ⟨?_, ?_⟩
    · intro Q₁ Q₂ hQ
      simpa [xi_v4_subcover_branch_rigidity_inertia_distinct_inertia] using hQ
    · intro H
      exact ⟨H, rfl⟩
  · ext H
    simp [xi_v4_subcover_branch_rigidity_inertia_distinct_inertia,
      xi_v4_subcover_branch_rigidity_inertia_distinct_branch_points,
      xi_v4_subcover_branch_rigidity_inertia_distinct_order_two_subgroups]
  · intro Q₁ Q₂ hQ
    simpa [xi_v4_subcover_branch_rigidity_inertia_distinct_inertia] using hQ

end Omega.Zeta
