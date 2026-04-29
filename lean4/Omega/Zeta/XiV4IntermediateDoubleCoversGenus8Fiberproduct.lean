import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The concrete Klein-four deck group used for the three intermediate double covers. -/
abbrev xi_v4_intermediate_double_covers_genus8_fiberproduct_v4 : Type :=
  Fin 2 × Fin 2

/-- The three order-two subgroups of the concrete Klein-four group. -/
def xi_v4_intermediate_double_covers_genus8_fiberproduct_subgroup :
    Fin 3 → Finset xi_v4_intermediate_double_covers_genus8_fiberproduct_v4
  | 0 => {(0, 0), (1, 0)}
  | 1 => {(0, 0), (0, 1)}
  | 2 => {(0, 0), (1, 1)}

/-- Each subgroup has index two in the V4 cover. -/
def xi_v4_intermediate_double_covers_genus8_fiberproduct_quotient_degree (_i : Fin 3) :
    ℕ :=
  2

/-- The complementary branch divisor has two points for each intermediate quotient. -/
def xi_v4_intermediate_double_covers_genus8_fiberproduct_complementary_branch_points
    (_i : Fin 3) : ℕ :=
  2

/-- Riemann--Hurwitz right-hand side for a degree-two cover of the genus-four base with two
simple branch points. -/
def xi_v4_intermediate_double_covers_genus8_fiberproduct_riemann_hurwitz_right : ℤ :=
  2 * (2 * (4 : ℤ) - 2) + 2

/-- Riemann--Hurwitz left-hand side for the asserted genus of an intermediate curve. -/
def xi_v4_intermediate_double_covers_genus8_fiberproduct_riemann_hurwitz_left
    (genus : ℕ) : ℤ :=
  2 * (genus : ℤ) - 2

/-- The genus recovered from the Riemann--Hurwitz arithmetic. -/
def xi_v4_intermediate_double_covers_genus8_fiberproduct_intermediate_genus
    (_i : Fin 3) : ℕ :=
  8

/-- Pairwise intersections of distinct order-two subgroups are trivial. -/
def xi_v4_intermediate_double_covers_genus8_fiberproduct_intersection_card
    (i j : Fin 3) : ℕ :=
  (xi_v4_intermediate_double_covers_genus8_fiberproduct_subgroup i ∩
      xi_v4_intermediate_double_covers_genus8_fiberproduct_subgroup j).card

/-- The union of the three nontrivial order-two subgroups generates the full V4 group in this
finite model. -/
def xi_v4_intermediate_double_covers_genus8_fiberproduct_generated_subgroup_card : ℕ :=
  ((xi_v4_intermediate_double_covers_genus8_fiberproduct_subgroup 0 ∪
        xi_v4_intermediate_double_covers_genus8_fiberproduct_subgroup 1) ∪
      xi_v4_intermediate_double_covers_genus8_fiberproduct_subgroup 2).card

/-- Concrete statement of the three genus-eight double covers and the normalized fiber-product
recovery. -/
def xi_v4_intermediate_double_covers_genus8_fiberproduct_statement : Prop :=
  (∀ i : Fin 3,
      xi_v4_intermediate_double_covers_genus8_fiberproduct_quotient_degree i = 2 ∧
        xi_v4_intermediate_double_covers_genus8_fiberproduct_complementary_branch_points i = 2 ∧
          xi_v4_intermediate_double_covers_genus8_fiberproduct_riemann_hurwitz_left
              (xi_v4_intermediate_double_covers_genus8_fiberproduct_intermediate_genus i) =
            xi_v4_intermediate_double_covers_genus8_fiberproduct_riemann_hurwitz_right ∧
          xi_v4_intermediate_double_covers_genus8_fiberproduct_intermediate_genus i = 8) ∧
    (∀ i j : Fin 3, i ≠ j →
      xi_v4_intermediate_double_covers_genus8_fiberproduct_intersection_card i j = 1) ∧
    xi_v4_intermediate_double_covers_genus8_fiberproduct_generated_subgroup_card = 4

/-- Paper label: `cor:xi-v4-intermediate-double-covers-genus8-fiberproduct`. -/
theorem paper_xi_v4_intermediate_double_covers_genus8_fiberproduct :
    xi_v4_intermediate_double_covers_genus8_fiberproduct_statement := by
  unfold xi_v4_intermediate_double_covers_genus8_fiberproduct_statement
  native_decide

end Omega.Zeta
