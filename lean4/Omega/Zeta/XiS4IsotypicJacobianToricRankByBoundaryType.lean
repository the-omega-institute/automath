import Mathlib.Tactic

namespace Omega.Zeta

/-- The three boundary types in the S4 semistable rank table. -/
inductive xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_boundary
    where
  | r1
  | r2
  | r3
  deriving DecidableEq, Fintype

/-- The four rational S4 isotypic coordinates used for the toric-rank table. -/
inductive xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_irrep
    where
  | eps
  | rho2
  | rho3
  | rho3p
  deriving DecidableEq, Fintype

open xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_boundary
open xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_irrep

/-- The paper's boundary label `r ∈ {1,2,3}`. -/
def xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_boundaryLabel :
    xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_boundary → ℕ
  | r1 => 1
  | r2 => 2
  | r3 => 3

/-- The four-coordinate toric-rank table `(t_eps,t_rho2,t_rho3,t_rho3p)`. -/
def xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_rank :
    xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_boundary →
      xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_irrep → ℕ
  | r1, eps => 1
  | r1, rho2 => 2
  | r1, rho3 => 3
  | r1, rho3p => 6
  | r2, eps => 0
  | r2, rho2 => 0
  | r2, rho3 => 3
  | r2, rho3p => 3
  | r3, eps => 1
  | r3, rho2 => 0
  | r3, rho3 => 0
  | r3, rho3p => 3

/-- The displayed S4 isotypic toric-rank table, as a finite proposition. -/
def xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_statement : Prop :=
  (xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_boundaryLabel r1 = 1 ∧
    xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_rank r1 eps = 1 ∧
      xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_rank r1 rho2 = 2 ∧
        xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_rank r1 rho3 = 3 ∧
          xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_rank r1 rho3p = 6) ∧
    (xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_boundaryLabel r2 = 2 ∧
      xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_rank r2 eps = 0 ∧
        xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_rank r2 rho2 = 0 ∧
          xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_rank r2 rho3 = 3 ∧
            xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_rank r2 rho3p = 3) ∧
      (xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_boundaryLabel r3 = 3 ∧
        xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_rank r3 eps = 1 ∧
          xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_rank r3 rho2 = 0 ∧
            xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_rank r3 rho3 = 0 ∧
              xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_rank r3 rho3p = 3)

/-- Paper label: `thm:xi-s4-isotypic-jacobian-toric-rank-by-boundary-type`. -/
theorem paper_xi_s4_isotypic_jacobian_toric_rank_by_boundary_type :
    xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_statement := by
  simp [xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_statement,
    xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_boundaryLabel,
    xi_s4_isotypic_jacobian_toric_rank_by_boundary_type_rank]

end Omega.Zeta
