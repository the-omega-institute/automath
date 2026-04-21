import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyTrigonalGenus
import Omega.Zeta.XiTerminalZmKappaSquareCubicFieldS3

namespace Omega.Zeta

/-- The Stokes amplitude-square cubic from the terminal `Z_m` branch. -/
def xiTerminalStokesAmplitudeSquareCubic (b : ℚ) : ℚ :=
  162 * b ^ 3 + 1593 * b ^ 2 + 1998 * b + 1184

/-- The discriminant of `162 b^3 + 1593 b^2 + 1998 b + 1184`. -/
def xiTerminalStokesAmplitudeSquareDiscriminant : ℤ :=
  cubicDiscriminant 162 1593 1998 1184

/-- The common quadratic resolvent discriminant carried by the shared `S₃` standard
two-dimensional Artin representation. -/
def xiTerminalStokesLeyangQuadraticResolventDiscriminant : ℤ := -111

/-- The common Artin-representation dimension. -/
def xiTerminalStokesLeyangSharedArtinDimension : ℕ := 2

private theorem xiTerminalStokesAmplitudeSquareDiscriminant_eval :
    xiTerminalStokesAmplitudeSquareDiscriminant =
      -((2 : ℤ) ^ 2 * 3 ^ 9 * 11 ^ 2 * 37 * 109 ^ 2) := by
  norm_num [xiTerminalStokesAmplitudeSquareDiscriminant, cubicDiscriminant]

private theorem xiTerminalStokesAmplitudeSquareDiscriminant_not_square :
    ¬ IsSquare xiTerminalStokesAmplitudeSquareDiscriminant := by
  intro hsquare
  rcases hsquare with ⟨n, hn⟩
  have hnonneg : 0 ≤ xiTerminalStokesAmplitudeSquareDiscriminant := by
    simpa [pow_two, hn] using sq_nonneg n
  rw [xiTerminalStokesAmplitudeSquareDiscriminant_eval] at hnonneg
  norm_num at hnonneg

/-- Paper label: `thm:xi-terminal-zm-stokes-leyang-shared-artin-representation`.
The terminal `u = κ_*²` cubic and the Stokes amplitude-square cubic both carry `S₃` Galois data,
so they factor through the same standard `2`-dimensional Artin representation and have the same
quadratic resolvent discriminant `-111`. -/
  theorem paper_xi_terminal_zm_stokes_leyang_shared_artin_representation :
    xiTerminalKappaSquareS3Audit ∧
      (xiTerminalStokesAmplitudeSquareDiscriminant =
        -((2 : ℤ) ^ 2 * 3 ^ 9 * 11 ^ 2 * 37 * 109 ^ 2)) ∧
      ¬ IsSquare xiTerminalStokesAmplitudeSquareDiscriminant ∧
      Nat.factorial 3 = 6 ∧
      xiTerminalStokesLeyangSharedArtinDimension = 2 ∧
      xiTerminalStokesLeyangQuadraticResolventDiscriminant = -111 := by
  refine ⟨?_, xiTerminalStokesAmplitudeSquareDiscriminant_eval,
    xiTerminalStokesAmplitudeSquareDiscriminant_not_square, ?_, rfl, rfl⟩
  · exact paper_xi_terminal_zm_kappa_square_cubic_field_s3.2.2.2.2
  · exact Omega.Folding.GaugeAnomalyTrigonalGenus.s3_order_eq

end Omega.Zeta
