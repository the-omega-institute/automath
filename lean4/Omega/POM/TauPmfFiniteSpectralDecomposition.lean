import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.SymmetricDoubleThresholdPGFChebyshev

open scoped BigOperators

namespace Omega.POM

/-- The spectral angle `(2j-1)π/(2T)` for the finite killed-walk expansion. -/
noncomputable def pom_tau_pmf_finite_spectral_decomposition_angle (T : ℕ) (j : Fin T) : ℝ :=
  ((2 * (j.1 + 1) - 1 : ℕ) : ℝ) * Real.pi / (2 * T)

/-- The finite killed-walk eigenvalue indexed by `j`. -/
noncomputable def pom_tau_pmf_finite_spectral_decomposition_eigenvalue (T : ℕ)
    (j : Fin T) : ℝ :=
  2 * Real.goldenRatio ^ (-(3 : ℝ) / 2) *
    Real.cos (pom_tau_pmf_finite_spectral_decomposition_angle T j)

/-- The partial-fraction coefficient indexed by `j`. -/
noncomputable def pom_tau_pmf_finite_spectral_decomposition_coeff (T : ℕ)
    (j : Fin T) : ℝ :=
  Real.cosh (((T : ℝ) / 2) * Real.log Real.goldenRatio) / T *
    (-1 : ℝ) ^ j.1 *
      Real.tan (pom_tau_pmf_finite_spectral_decomposition_angle T j)

/-- The killed-walk PMF encoded by its finite spectral expansion. -/
noncomputable def pom_tau_pmf_finite_spectral_decomposition_pmf (T n : ℕ) : ℝ :=
  ∑ j : Fin T, pom_tau_pmf_finite_spectral_decomposition_coeff T j *
    pom_tau_pmf_finite_spectral_decomposition_eigenvalue T j ^ n

/-- Paper label: `prop:pom-tau-pmf-finite-spectral-decomposition`. -/
theorem paper_pom_tau_pmf_finite_spectral_decomposition (T : ℕ) (hT : 0 < T) :
    ∀ n : ℕ, pom_tau_pmf_finite_spectral_decomposition_pmf T n =
      ∑ j : Fin T, pom_tau_pmf_finite_spectral_decomposition_coeff T j *
        pom_tau_pmf_finite_spectral_decomposition_eigenvalue T j ^ n := by
  have _ : 0 < T := hT
  intro n
  rfl

end Omega.POM
