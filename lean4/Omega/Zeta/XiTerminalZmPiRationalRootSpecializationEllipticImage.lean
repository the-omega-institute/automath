import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmLeyangEllipticStructure

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-pi-rational-root-specialization-elliptic-image`. -/
theorem paper_xi_terminal_zm_pi_rational_root_specialization_elliptic_image (y0 : ℚ) :
    (∃ lam : ℚ, lam ^ 4 - lam ^ 3 - (2 * y0 + 1) * lam ^ 2 + lam + y0 * (y0 + 1) = 0) ↔
      ∃ x u : ℚ, u ^ 2 + u = x ^ 3 - x ∧ y0 = x ^ 2 + u := by
  constructor
  · rintro ⟨lam, hlam⟩
    refine ⟨lam, y0 - lam ^ 2, ?_, by ring⟩
    have hrewrite :
        lam ^ 4 - lam ^ 3 - (2 * y0 + 1) * lam ^ 2 + lam + y0 * (y0 + 1) =
          (y0 - lam ^ 2) ^ 2 + (y0 - lam ^ 2) - (lam ^ 3 - lam) := by
      ring
    linarith
  · rintro ⟨x, u, hu, hy⟩
    refine ⟨x, ?_⟩
    calc
      x ^ 4 - x ^ 3 - (2 * y0 + 1) * x ^ 2 + x + y0 * (y0 + 1)
          = x ^ 4 - x ^ 3 - (2 * (x ^ 2 + u) + 1) * x ^ 2 + x + (x ^ 2 + u) * ((x ^ 2 + u) + 1) := by
              simp [hy]
      _ = u ^ 2 + u - (x ^ 3 - x) := by ring
      _ = 0 := by linarith

end Omega.Zeta
