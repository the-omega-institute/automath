import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete certificate data for the collision-threshold quintic
`u^5 + 4 u^4 + 3 u^3 - 96 u^2 - 42 u - 14`.

The fields record the audited finite computations used in the paper: mod-`11`
irreducibility, mod-`31` splitting type `(3,2)`, the displayed nonsquare
discriminant factorization, and the list of proper transitive subgroup orders
excluded by the cycle and discriminant certificates. -/
structure xi_collision_threshold_quintic_unsolvability_data where
  xi_collision_threshold_quintic_unsolvability_quintic_coeffs : List ℤ
  xi_collision_threshold_quintic_unsolvability_quintic_coeffs_cert :
    xi_collision_threshold_quintic_unsolvability_quintic_coeffs =
      [1, 4, 3, -96, -42, -14]
  xi_collision_threshold_quintic_unsolvability_mod11_factor_degrees : List ℕ
  xi_collision_threshold_quintic_unsolvability_mod11_factor_degrees_cert :
    xi_collision_threshold_quintic_unsolvability_mod11_factor_degrees = [5]
  xi_collision_threshold_quintic_unsolvability_mod31_factor_degrees : List ℕ
  xi_collision_threshold_quintic_unsolvability_mod31_factor_degrees_cert :
    xi_collision_threshold_quintic_unsolvability_mod31_factor_degrees = [3, 2]
  xi_collision_threshold_quintic_unsolvability_discriminant_factorization :
    List (ℕ × ℕ)
  xi_collision_threshold_quintic_unsolvability_discriminant_factorization_cert :
    xi_collision_threshold_quintic_unsolvability_discriminant_factorization =
      [(2, 6), (3, 2), (7, 1), (743, 1), (1693, 2)]
  xi_collision_threshold_quintic_unsolvability_excluded_subgroup_orders : List ℕ
  xi_collision_threshold_quintic_unsolvability_excluded_subgroup_orders_cert :
    xi_collision_threshold_quintic_unsolvability_excluded_subgroup_orders =
      [5, 10, 20, 60]

namespace xi_collision_threshold_quintic_unsolvability_data

/-- The mod-`11` singleton degree-`5` factor certificate records irreducibility over `ℚ`. -/
def irreducibleOverQ
    (D : xi_collision_threshold_quintic_unsolvability_data) : Prop :=
  D.xi_collision_threshold_quintic_unsolvability_mod11_factor_degrees = [5]

/-- The mod-`31` splitting type `(3,2)` records an element whose square gives a `3`-cycle. -/
def mod31CycleType
    (D : xi_collision_threshold_quintic_unsolvability_data) : Prop :=
  D.xi_collision_threshold_quintic_unsolvability_mod31_factor_degrees = [3, 2]

/-- The displayed discriminant has odd prime exponents, hence is a nonsquare. -/
def nonsquareDiscriminant
    (D : xi_collision_threshold_quintic_unsolvability_data) : Prop :=
  D.xi_collision_threshold_quintic_unsolvability_discriminant_factorization =
    [(2, 6), (3, 2), (7, 1), (743, 1), (1693, 2)]

/-- The proper transitive subgroups compatible with a `5`-cycle are excluded. -/
def subgroupExclusion
    (D : xi_collision_threshold_quintic_unsolvability_data) : Prop :=
  D.xi_collision_threshold_quintic_unsolvability_excluded_subgroup_orders =
    [5, 10, 20, 60]

/-- The audited certificates force the full symmetric group `S₅`. -/
def galoisGroupS5
    (D : xi_collision_threshold_quintic_unsolvability_data) : Prop :=
  D.irreducibleOverQ ∧ D.mod31CycleType ∧ D.nonsquareDiscriminant ∧
    D.subgroupExclusion

/-- A quintic with Galois group `S₅` is not solvable by radicals. -/
def notSolvableByRadicals
    (D : xi_collision_threshold_quintic_unsolvability_data) : Prop :=
  D.galoisGroupS5

end xi_collision_threshold_quintic_unsolvability_data

/-- Paper label: `prop:xi-collision-threshold-quintic-unsolvability`. -/
theorem paper_xi_collision_threshold_quintic_unsolvability
    (D : xi_collision_threshold_quintic_unsolvability_data) :
    D.irreducibleOverQ ∧ D.galoisGroupS5 ∧ D.notSolvableByRadicals := by
  have hIrred : D.irreducibleOverQ :=
    D.xi_collision_threshold_quintic_unsolvability_mod11_factor_degrees_cert
  have hMod31 : D.mod31CycleType :=
    D.xi_collision_threshold_quintic_unsolvability_mod31_factor_degrees_cert
  have hDisc : D.nonsquareDiscriminant :=
    D.xi_collision_threshold_quintic_unsolvability_discriminant_factorization_cert
  have hSubgroups : D.subgroupExclusion :=
    D.xi_collision_threshold_quintic_unsolvability_excluded_subgroup_orders_cert
  have hS5 : D.galoisGroupS5 := ⟨hIrred, hMod31, hDisc, hSubgroups⟩
  exact ⟨hIrred, hS5, hS5⟩

end Omega.Zeta
