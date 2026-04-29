import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmKappaSquareCubicFieldS3
import Omega.Zeta.XiTerminalZmStokesLeyangSharedArtinRepresentation
import Omega.Zeta.XiTimePart9gLeyangCubicDiscriminant

namespace Omega.DerivedConsequences

/-- Paper label: `thm:derived-leyang-cubic-models-common-quadratic-resolvent`. -/
theorem paper_derived_leyang_cubic_models_common_quadratic_resolvent :
    Omega.Zeta.xiTerminalKappaSquareDiscriminant = -((2 : ℤ) ^ 6 * 3 ^ 9 * 37) ∧
      Omega.Zeta.xiTerminalStokesAmplitudeSquareDiscriminant =
        -((2 : ℤ) ^ 2 * 3 ^ 9 * 11 ^ 2 * 37 * 109 ^ 2) ∧
      Omega.Zeta.xiTimePart9gLeyangCubicDiscriminant = -((3 : ℤ) ^ 9 * 31 ^ 2 * 37) ∧
      Omega.Zeta.xiTerminalStokesLeyangQuadraticResolventDiscriminant = -111 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Omega.Zeta.paper_xi_terminal_zm_kappa_square_cubic_field_s3.2.2.2.1
  · exact Omega.Zeta.paper_xi_terminal_zm_stokes_leyang_shared_artin_representation.2.1
  · exact Omega.Zeta.paper_xi_time_part9g_leyang_cubic_discriminant.1
  · exact Omega.Zeta.paper_xi_terminal_zm_stokes_leyang_shared_artin_representation.2.2.2.2.2

end Omega.DerivedConsequences
