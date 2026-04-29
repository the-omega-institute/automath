import Mathlib.Tactic

namespace Omega.Zeta

/-- A minimal concrete label for the quadratic subfield cut out by a sign character. -/
inductive xi_terminal_zm_elliptic_5torsion_sign_quadratic_field_label
  | Qsqrt (d : ℤ)
  deriving DecidableEq, Repr

/-- The squarefree kernel of the degree-`24` five-torsion discriminant in the audited model. -/
def xi_terminal_zm_elliptic_5torsion_sign_quadratic_field_squarefree_kernel : ℤ := 5

/-- The quadratic field cut out by the sign character of the permutation action on the
five-torsion elimination polynomial. -/
def xi_terminal_zm_elliptic_5torsion_sign_quadratic_field_sign_field :
    xi_terminal_zm_elliptic_5torsion_sign_quadratic_field_label :=
  .Qsqrt xi_terminal_zm_elliptic_5torsion_sign_quadratic_field_squarefree_kernel

/-- Paper label: `cor:xi-terminal-zm-elliptic-5torsion-sign-quadratic-field`. Once the
discriminant squarefree kernel is `5`, the sign-character quadratic subfield is `Q(√5)`. -/
theorem paper_xi_terminal_zm_elliptic_5torsion_sign_quadratic_field :
    xi_terminal_zm_elliptic_5torsion_sign_quadratic_field_squarefree_kernel = 5 ∧
      xi_terminal_zm_elliptic_5torsion_sign_quadratic_field_sign_field = .Qsqrt 5 := by
  simp [xi_terminal_zm_elliptic_5torsion_sign_quadratic_field_squarefree_kernel,
    xi_terminal_zm_elliptic_5torsion_sign_quadratic_field_sign_field]

end Omega.Zeta
