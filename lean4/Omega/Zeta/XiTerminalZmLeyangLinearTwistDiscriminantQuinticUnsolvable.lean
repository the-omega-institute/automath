import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`cor:xi-terminal-zm-leyang-linear-twist-discriminant-quintic-unsolvable`. -/
theorem paper_xi_terminal_zm_leyang_linear_twist_discriminant_quintic_unsolvable
    (D_has_S5_galois_closure D_not_solvable_by_radicals : Prop)
    (hS5 : D_has_S5_galois_closure)
    (hunsolv : D_has_S5_galois_closure → D_not_solvable_by_radicals) :
    D_has_S5_galois_closure ∧ D_not_solvable_by_radicals := by
  exact ⟨hS5, hunsolv hS5⟩

end Omega.Zeta
