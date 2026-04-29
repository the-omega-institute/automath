import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The positive Fourier multipoles of `u_t - 1`. -/
abbrev xi_poisson_cauchy_chi2_spectrum_multipole_positive_modes (n : ℕ) :=
  Fin n → ℂ

/-- The paired positive/negative Fourier spectrum coming from the reality condition
`c_{-k} = conj c_k`. -/
def xi_poisson_cauchy_chi2_spectrum_multipole_fourier_coefficient
    {n : ℕ}
    (m : xi_poisson_cauchy_chi2_spectrum_multipole_positive_modes n) :
    Sum (Fin n) (Fin n) → ℂ
  | Sum.inl k => m k
  | Sum.inr k => Complex.mk (m k).re (-(m k).im)

/-- The positive-mode Parseval energy. -/
def xi_poisson_cauchy_chi2_spectrum_multipole_positive_energy
    {n : ℕ}
    (m : xi_poisson_cauchy_chi2_spectrum_multipole_positive_modes n) : ℝ :=
  ∑ k, Complex.normSq (m k)

/-- The `χ²` energy after Cayley transport to Haar measure on the circle. -/
def xi_poisson_cauchy_chi2_spectrum_multipole_chi2_energy
    {n : ℕ}
    (m : xi_poisson_cauchy_chi2_spectrum_multipole_positive_modes n) : ℝ :=
  ∑ k : Sum (Fin n) (Fin n),
    Complex.normSq
      (xi_poisson_cauchy_chi2_spectrum_multipole_fourier_coefficient m k)

/-- Paper label: `prop:xi-poisson-cauchy-chi2-spectrum-multipole`. After the Cayley change of
variables, the negative Fourier modes are the conjugates of the positive ones, so the zero-free
Parseval energy is exactly twice the positive multipole energy. -/
theorem paper_xi_poisson_cauchy_chi2_spectrum_multipole (n : ℕ)
    (m : xi_poisson_cauchy_chi2_spectrum_multipole_positive_modes n) :
    xi_poisson_cauchy_chi2_spectrum_multipole_chi2_energy m =
      2 * xi_poisson_cauchy_chi2_spectrum_multipole_positive_energy m := by
  unfold xi_poisson_cauchy_chi2_spectrum_multipole_chi2_energy
    xi_poisson_cauchy_chi2_spectrum_multipole_positive_energy
    xi_poisson_cauchy_chi2_spectrum_multipole_fourier_coefficient
  rw [Fintype.sum_sum_type]
  simp [Complex.normSq, two_mul]

end Omega.Zeta
