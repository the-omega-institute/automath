import Mathlib.Tactic
import Omega.Folding.KilloLeyangTwoBranchFieldsProductGalois
import Omega.Zeta.XiTerminalZmKappaSquareCubicFieldS3
import Omega.Zeta.XiTerminalZmStokesLeyangCommonQuadraticResolvent
import Omega.Zeta.XiTerminalZmStokesLeyangSharedArtinRepresentation

namespace Omega.Folding

/-- The explicit rational expression of the amplitude square `b = B²` in terms of `u = κ_*²`. -/
def killo_leyang_b_square_cubic_and_rational_intertwine_b_from_u (u : ℚ) : ℚ :=
  -2 * (24708 * u ^ 2 - 28628 * u + 7733) / (51084 * u ^ 2 - 44412 * u + 8735)

/-- Paper-facing package for the Lee--Yang amplitude-square cubic and its rational intertwining
with the already audited `u = κ_*²` cubic. -/
def killo_leyang_b_square_cubic_and_rational_intertwine_statement : Prop :=
  (∀ u : ℚ,
      killo_leyang_b_square_cubic_and_rational_intertwine_b_from_u u =
        -2 * (24708 * u ^ 2 - 28628 * u + 7733) /
          (51084 * u ^ 2 - 44412 * u + 8735)) ∧
    (∀ b : ℚ,
      Omega.Zeta.xiTerminalStokesAmplitudeSquareCubic b =
        162 * b ^ 3 + 1593 * b ^ 2 + 1998 * b + 1184) ∧
    Omega.Zeta.xiTerminalStokesAmplitudeSquareDiscriminant =
      -((2 : ℤ) ^ 2 * 3 ^ 9 * 11 ^ 2 * 37 * 109 ^ 2) ∧
    ¬ IsSquare Omega.Zeta.xiTerminalStokesAmplitudeSquareDiscriminant ∧
    (∀ u : ℚ,
      Omega.Zeta.xiTerminalLambdaFromU u = 3 * (2 * u - 1) / (4 * (3 * u - 2))) ∧
    Omega.Zeta.xiTerminalKappaSquareDiscriminant = -((2 : ℤ) ^ 6 * 3 ^ 9 * 37) ∧
    Omega.Zeta.xiTerminalStokesLeyangQuadraticResolventDiscriminant = -111 ∧
    killoLeyangCubicQuadraticSubfieldDiscriminant = -111

/-- Paper label: `thm:killo-leyang-B-square-cubic-and-rational-intertwine`. -/
theorem paper_killo_leyang_b_square_cubic_and_rational_intertwine :
    killo_leyang_b_square_cubic_and_rational_intertwine_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    rfl
  · intro b
    rfl
  · exact Omega.Zeta.paper_xi_terminal_zm_stokes_leyang_shared_artin_representation.2.1
  · exact Omega.Zeta.paper_xi_terminal_zm_stokes_leyang_shared_artin_representation.2.2.1
  · exact Omega.Zeta.paper_xi_terminal_zm_kappa_square_cubic_field_s3.1
  · exact Omega.Zeta.paper_xi_terminal_zm_stokes_leyang_common_quadratic_resolvent.1
  · exact Omega.Zeta.paper_xi_terminal_zm_stokes_leyang_common_quadratic_resolvent.2.2
  · norm_num [killoLeyangCubicQuadraticSubfieldDiscriminant]

end Omega.Folding
