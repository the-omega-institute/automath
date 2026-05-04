import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete package for the `62d` collision/RH resultant template.  The branch point is an
integer root at which the collision cubic and the RH boundary constraint are both evaluated. -/
structure xi_time_part62d_collision_rh_resultant_template_data where
  xi_time_part62d_collision_rh_resultant_template_boundary : ℤ
  xi_time_part62d_collision_rh_resultant_template_branch : ℤ
  xi_time_part62d_collision_rh_resultant_template_offset : ℤ
  xi_time_part62d_collision_rh_resultant_template_collision_cubic : ℤ → ℤ
  xi_time_part62d_collision_rh_resultant_template_collision_quadratic : ℤ → ℤ
  xi_time_part62d_collision_rh_resultant_template_cubic_branch :
    xi_time_part62d_collision_rh_resultant_template_branch ^ 3 -
        xi_time_part62d_collision_rh_resultant_template_boundary *
          xi_time_part62d_collision_rh_resultant_template_branch +
          xi_time_part62d_collision_rh_resultant_template_offset =
      0
  xi_time_part62d_collision_rh_resultant_template_rh_boundary :
    xi_time_part62d_collision_rh_resultant_template_branch ^ 2 -
        xi_time_part62d_collision_rh_resultant_template_boundary =
      0
  xi_time_part62d_collision_rh_resultant_template_collision_factor :
    ∀ x : ℤ,
      xi_time_part62d_collision_rh_resultant_template_collision_cubic x =
        (x - xi_time_part62d_collision_rh_resultant_template_branch) *
          xi_time_part62d_collision_rh_resultant_template_collision_quadratic x

namespace xi_time_part62d_collision_rh_resultant_template_data

/-- The cubic branch constraint evaluated at an integer point. -/
def cubicConstraint (D : xi_time_part62d_collision_rh_resultant_template_data) (x : ℤ) :
    ℤ :=
  x ^ 3 - D.xi_time_part62d_collision_rh_resultant_template_boundary * x +
    D.xi_time_part62d_collision_rh_resultant_template_offset

/-- The RH boundary constraint paired with the branch cubic. -/
def rhConstraint (D : xi_time_part62d_collision_rh_resultant_template_data) (x : ℤ) :
    ℤ :=
  x ^ 2 - D.xi_time_part62d_collision_rh_resultant_template_boundary

/-- Resultant-vanishing certificate: the two integer polynomial constraints have a common root. -/
def resultant_vanishes (D : xi_time_part62d_collision_rh_resultant_template_data) : Prop :=
  ∃ x : ℤ, D.cubicConstraint x = 0 ∧ D.rhConstraint x = 0

/-- Specialized factorization of the collision cubic at the packaged branch. -/
def specialized_collision_factorization
    (D : xi_time_part62d_collision_rh_resultant_template_data) : Prop :=
  D.xi_time_part62d_collision_rh_resultant_template_collision_cubic
      D.xi_time_part62d_collision_rh_resultant_template_branch =
    0 ∧
    ∀ x : ℤ,
      D.xi_time_part62d_collision_rh_resultant_template_collision_cubic x =
        (x - D.xi_time_part62d_collision_rh_resultant_template_branch) *
          D.xi_time_part62d_collision_rh_resultant_template_collision_quadratic x

end xi_time_part62d_collision_rh_resultant_template_data

/-- Paper label: `prop:xi-time-part62d-collision-rh-resultant-template`. -/
theorem paper_xi_time_part62d_collision_rh_resultant_template
    (D : xi_time_part62d_collision_rh_resultant_template_data) :
    D.resultant_vanishes ∧ D.specialized_collision_factorization := by
  refine ⟨?_, ?_⟩
  · refine ⟨D.xi_time_part62d_collision_rh_resultant_template_branch, ?_, ?_⟩
    · simpa [xi_time_part62d_collision_rh_resultant_template_data.cubicConstraint]
        using D.xi_time_part62d_collision_rh_resultant_template_cubic_branch
    · simpa [xi_time_part62d_collision_rh_resultant_template_data.rhConstraint]
        using D.xi_time_part62d_collision_rh_resultant_template_rh_boundary
  · constructor
    · rw [D.xi_time_part62d_collision_rh_resultant_template_collision_factor]
      ring
    · intro x
      exact D.xi_time_part62d_collision_rh_resultant_template_collision_factor x

end Omega.Zeta
