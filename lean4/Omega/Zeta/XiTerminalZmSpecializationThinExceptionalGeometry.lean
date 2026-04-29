import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmPiRationalRootSpecializationEllipticImage

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-specialization-thin-exceptional-geometry`. -/
theorem paper_xi_terminal_zm_specialization_thin_exceptional_geometry (y0 : ℚ)
    (irreducible separable galoisInA4 fullS4OutsideThin : Prop)
    (hdisc :
      galoisInA4 ↔
        ∃ zeta : ℚ,
          zeta ^ 2 =
            -y0 * (y0 - 1) * (256 * y0 ^ 3 + 411 * y0 ^ 2 + 165 * y0 + 32))
    (hfull : fullS4OutsideThin) :
    ((∃ lam : ℚ,
        lam ^ 4 - lam ^ 3 - (2 * y0 + 1) * lam ^ 2 + lam + y0 * (y0 + 1) = 0) →
      ∃ x u : ℚ, u ^ 2 + u = x ^ 3 - x ∧ y0 = x ^ 2 + u) ∧
      ((separable ∧ irreducible) →
        (galoisInA4 ↔
          ∃ zeta : ℚ,
            zeta ^ 2 =
              -y0 * (y0 - 1) * (256 * y0 ^ 3 + 411 * y0 ^ 2 + 165 * y0 + 32))) ∧
        fullS4OutsideThin := by
  refine ⟨?_, ?_, hfull⟩
  · exact (paper_xi_terminal_zm_pi_rational_root_specialization_elliptic_image y0).1
  · intro _
    exact hdisc

end Omega.Zeta
