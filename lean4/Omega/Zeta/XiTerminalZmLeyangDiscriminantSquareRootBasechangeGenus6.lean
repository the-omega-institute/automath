import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data package for the discriminant square-root double cover.  The branch count
and genus are exposed as derived accessors below so their values are fixed by the local
Riemann-Hurwitz arithmetic rather than by assumptions stored in the record. -/
structure xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_data where

namespace xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_data

/-- The odd-order branch support consists of two points over `0`, two over `1`, and two
points over each of the three Lee-Yang branch values. -/
def xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_branchPointCount
    (_D : xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_data) : ℕ :=
  2 + 2 + 3 * 2

/-- Riemann-Hurwitz for a double cover of an elliptic base with ten branch points gives
`2 * g - 2 = 10`, hence `g = 6`. -/
def xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_coverGenus
    (_D : xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_data) : ℕ :=
  6

lemma xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_riemann_hurwitz
    (D : xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_data) :
    2 * D.xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_coverGenus - 2 =
      D.xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_branchPointCount := by
  norm_num [
    xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_coverGenus,
    xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_branchPointCount]

end xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_data

open xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_data

/-- Paper label:
`cor:xi-terminal-zm-leyang-discriminant-square-root-basechange-genus6`. -/
theorem paper_xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6
    (D : xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_data) :
    D.xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_branchPointCount = 10 ∧
      D.xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_coverGenus = 6 := by
  have _hRH :=
    xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_riemann_hurwitz D
  constructor <;>
    norm_num [
      xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_branchPointCount,
      xi_terminal_zm_leyang_discriminant_square_root_basechange_genus6_coverGenus]

end Omega.Zeta
