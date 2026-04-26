import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmLeyangEllipticStructure

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-zm-leyang-elliptic-37-modularity-monodromy-langlands`. This is
the algebraic equivalence obtained by the Lee--Yang coordinate change `x = λ`, `v = y - λ²`,
repackaged in the exact zero-locus form used by the paper statement. -/
theorem paper_xi_terminal_zm_leyang_elliptic_37_modularity_monodromy_langlands
    (lam y : ℤ) :
    let x := lam
    let v := y - lam ^ 2
    lam ^ 4 - lam ^ 3 - (2 * y + 1) * lam ^ 2 + lam + y * (y + 1) = 0 ↔
      v ^ 2 + v = x ^ 3 - x := by
  dsimp
  have hstructure := (paper_xi_terminal_zm_leyang_elliptic_structure lam y).1
  constructor
  · intro hquartic
    rw [hstructure] at hquartic
    linarith
  · intro helliptic
    rw [hstructure]
    linarith

end Omega.Zeta
