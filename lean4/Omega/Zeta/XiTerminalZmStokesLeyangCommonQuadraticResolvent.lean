import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmKappaSquareCubicFieldS3
import Omega.Zeta.XiTerminalZmStokesLeyangSharedArtinRepresentation

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-stokes-leyang-common-quadratic-resolvent`. -/
theorem paper_xi_terminal_zm_stokes_leyang_common_quadratic_resolvent :
    xiTerminalKappaSquareDiscriminant = -((2 : ℤ) ^ 6 * 3 ^ 9 * 37) ∧
      xiTerminalStokesAmplitudeSquareDiscriminant =
        -((2 : ℤ) ^ 2 * 3 ^ 9 * 11 ^ 2 * 37 * 109 ^ 2) ∧
      xiTerminalStokesLeyangQuadraticResolventDiscriminant = -111 := by
  refine ⟨?_, ?_, ?_⟩
  · exact paper_xi_terminal_zm_kappa_square_cubic_field_s3.2.2.2.1
  · exact paper_xi_terminal_zm_stokes_leyang_shared_artin_representation.2.1
  · exact paper_xi_terminal_zm_stokes_leyang_shared_artin_representation.2.2.2.2.2

end Omega.Zeta
