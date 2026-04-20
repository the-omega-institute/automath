import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-zm-leyang-elliptic-structure`.

The Lee--Yang quartic becomes the affine model `u^2 + u = x^3 - x` after the coordinate change
`x = λ`, `u = y - λ^2`, and `w = 2u + 1` converts this to the short Weierstrass form used later.
-/
theorem paper_xi_terminal_zm_leyang_elliptic_structure (lam y : Int) :
    let x := lam
    let u := y - lam ^ 2
    let w := 2 * u + 1
    (lam ^ 4 - lam ^ 3 - (2 * y + 1) * lam ^ 2 + lam + y * (y + 1) =
        u ^ 2 + u - (x ^ 3 - x)) ∧
      (4 * (lam ^ 4 - lam ^ 3 - (2 * y + 1) * lam ^ 2 + lam + y * (y + 1)) =
        w ^ 2 - (4 * x ^ 3 - 4 * x + 1)) := by
  dsimp
  constructor <;> ring_nf

end Omega.Zeta
