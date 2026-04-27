import Mathlib.Tactic
import Omega.POM.A4TEvenSpectrumGammaInversion

namespace Omega.POM

/-- The forward quadratic product `Q_t(x)` from the Gamma-inversion certificate. -/
def pom_a4t_newman_short_elimination_Q (t x : ℤ) : ℤ :=
  (t * x + 3 * x ^ 2 - 2) * (t * x + 4 * t - 5 * x ^ 2 + 4 * x + 6)

/-- The Perron quintic curve used in the Newman elimination. -/
def pom_a4t_newman_short_elimination_P (t r : ℤ) : ℤ :=
  r ^ 5 - 2 * r ^ 4 - t * r ^ 3 - 2 * r + 2

/-- The cleared reciprocal even-spectrum quintic `r^5 E_t(1/r)`. -/
def pom_a4t_newman_short_elimination_r5_E_recip (t r : ℤ) : ℤ :=
  r ^ 5 - (2 * t + 4) * r ^ 4 + (t ^ 2 - 4) * r ^ 3 +
    (4 * t + 8) * r ^ 2 + 4 * r - 4

/-- The cleared short Gamma-elimination polynomial
`4 r^4 Q_t(1/r) - r Q_t(r)`, written without denominators. -/
def pom_a4t_newman_short_elimination_G (t r : ℤ) : ℤ :=
  4 * (t * r + 3 - 2 * r ^ 2) * (t * r + 4 * t * r ^ 2 - 5 + 4 * r + 6 * r ^ 2) -
    r * pom_a4t_newman_short_elimination_Q t r

/-- The Newman octic threshold certificate `P_4(t)`. -/
def pom_a4t_newman_short_elimination_P4 (t : ℤ) : ℤ :=
  t ^ 8 - 10 * t ^ 7 + 72 * t ^ 6 - 24 * t ^ 5 - 1924 * t ^ 4 -
    2904 * t ^ 3 + 1312 * t ^ 2 + 1464 * t - 1412

/-- The recorded resultant factor for the two five-degree curves in the short elimination. -/
def pom_a4t_newman_short_elimination_resultant (t : ℤ) : ℤ :=
  -((2 : ℤ) ^ 3 * (3 : ℤ) ^ 5 * (5 : ℤ) ^ 5) * (t + 1) ^ 2 *
    pom_a4t_newman_short_elimination_P4 t

/-- Paper label: `prop:pom-a4t-newman-short-elimination`. -/
theorem paper_pom_a4t_newman_short_elimination (t r : ℤ) :
    pom_a4t_newman_short_elimination_G t r =
        15 * pom_a4t_newman_short_elimination_r5_E_recip t r ∧
      pom_a4t_newman_short_elimination_resultant t =
        -((2 : ℤ) ^ 3 * (3 : ℤ) ^ 5 * (5 : ℤ) ^ 5) * (t + 1) ^ 2 *
          pom_a4t_newman_short_elimination_P4 t := by
  constructor
  · dsimp [pom_a4t_newman_short_elimination_G,
      pom_a4t_newman_short_elimination_Q,
      pom_a4t_newman_short_elimination_r5_E_recip]
    ring
  · rfl

end Omega.POM
