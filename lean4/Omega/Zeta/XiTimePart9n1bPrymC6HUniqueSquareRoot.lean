import Mathlib.Tactic

namespace Omega.Zeta

/-- The four visible factors in the finite Prym square table. -/
inductive xi_time_part9n1b_prym_c6h_unique_square_root_visible_factor where
  | O
  | J
  | Z
  | JZ
  deriving DecidableEq

/-- The Prym factor `Prym(C6/H)` as it appears in the visible square table. -/
def xi_time_part9n1b_prym_c6h_unique_square_root_prymC6H :
    xi_time_part9n1b_prym_c6h_unique_square_root_visible_factor :=
  xi_time_part9n1b_prym_c6h_unique_square_root_visible_factor.Z

/-- The visible squaring table; only `JZ` squares to `Prym(C6/H)`. -/
def xi_time_part9n1b_prym_c6h_unique_square_root_square :
    xi_time_part9n1b_prym_c6h_unique_square_root_visible_factor →
      xi_time_part9n1b_prym_c6h_unique_square_root_visible_factor
  | xi_time_part9n1b_prym_c6h_unique_square_root_visible_factor.O =>
      xi_time_part9n1b_prym_c6h_unique_square_root_visible_factor.O
  | xi_time_part9n1b_prym_c6h_unique_square_root_visible_factor.J =>
      xi_time_part9n1b_prym_c6h_unique_square_root_visible_factor.J
  | xi_time_part9n1b_prym_c6h_unique_square_root_visible_factor.Z =>
      xi_time_part9n1b_prym_c6h_unique_square_root_visible_factor.O
  | xi_time_part9n1b_prym_c6h_unique_square_root_visible_factor.JZ =>
      xi_time_part9n1b_prym_c6h_unique_square_root_prymC6H

/-- Paper label: `cor:xi-time-part9n1b-prym-c6h-unique-square-root`. -/
theorem paper_xi_time_part9n1b_prym_c6h_unique_square_root
    (A : xi_time_part9n1b_prym_c6h_unique_square_root_visible_factor)
    (hA :
      xi_time_part9n1b_prym_c6h_unique_square_root_square A =
        xi_time_part9n1b_prym_c6h_unique_square_root_prymC6H) :
    A = xi_time_part9n1b_prym_c6h_unique_square_root_visible_factor.JZ := by
  cases A <;> simp [xi_time_part9n1b_prym_c6h_unique_square_root_square,
    xi_time_part9n1b_prym_c6h_unique_square_root_prymC6H] at hA ⊢

end Omega.Zeta
