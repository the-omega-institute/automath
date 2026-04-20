import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-a4t-even-spectrum-gamma-inversion`. Clearing the reciprocal term
`u^4 * Q(1 / u)` produces an explicit polynomial identity over `ℤ`. -/
theorem paper_pom_a4t_even_spectrum_gamma_inversion (t u : ℤ) :
    let E := 1 - (2 * t + 4) * u + (t ^ 2 - 4) * u ^ 2 + (4 * t + 8) * u ^ 3 + 4 * u ^ 4 -
      4 * u ^ 5
    let Q := (t * u + 3 * u ^ 2 - 2) * (t * u + 4 * t - 5 * u ^ 2 + 4 * u + 6)
    let Qrev := 4 * t ^ 2 * u ^ 3 + t ^ 2 * u ^ 2 - 8 * t * u ^ 4 + 4 * t * u ^ 3 +
      16 * t * u ^ 2 - 2 * t * u - 12 * u ^ 4 - 8 * u ^ 3 + 28 * u ^ 2 + 12 * u - 15
    15 * E = 4 * u * Q - Qrev := by
  dsimp
  ring

end Omega.POM
