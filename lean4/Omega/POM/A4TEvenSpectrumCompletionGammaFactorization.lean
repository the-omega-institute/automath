import Mathlib.Tactic

namespace Omega.POM

/-- The even determinant evaluator used in the completed `A₄(t)` spectrum. -/
def pom_a4t_even_spectrum_completion_gamma_factorization_E (t u : ℤ) : ℤ :=
  1 - (2 * t + 4) * u + (t ^ 2 - 4) * u ^ 2 + (4 * t + 8) * u ^ 3 +
    4 * u ^ 4 - 4 * u ^ 5

/-- The cleared reciprocal evaluator `u^5 E_t(1/u)`. -/
def pom_a4t_even_spectrum_completion_gamma_factorization_E_reverse (t u : ℤ) : ℤ :=
  u ^ 5 - (2 * t + 4) * u ^ 4 + (t ^ 2 - 4) * u ^ 3 + (4 * t + 8) * u ^ 2 +
    4 * u - 4

/-- The completed even-spectrum polynomial `Xi_t(u) = u^5 E_t(1/u) + 4 E_t(u)`. -/
def pom_a4t_even_spectrum_completion_gamma_factorization_xi (t u : ℤ) : ℤ :=
  pom_a4t_even_spectrum_completion_gamma_factorization_E_reverse t u +
    4 * pom_a4t_even_spectrum_completion_gamma_factorization_E t u

/-- Paper label: `prop:pom-a4t-even-spectrum-completion-gamma-factorization`. -/
theorem paper_pom_a4t_even_spectrum_completion_gamma_factorization (t u : ℤ) :
    pom_a4t_even_spectrum_completion_gamma_factorization_xi t u =
      u * (t * u + 3 * u ^ 2 - 2) * (t * u + 4 * t - 5 * u ^ 2 + 4 * u + 6) := by
  unfold pom_a4t_even_spectrum_completion_gamma_factorization_xi
    pom_a4t_even_spectrum_completion_gamma_factorization_E_reverse
    pom_a4t_even_spectrum_completion_gamma_factorization_E
  ring

end Omega.POM
