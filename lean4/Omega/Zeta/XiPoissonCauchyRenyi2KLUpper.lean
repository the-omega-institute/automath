import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiPoissonCauchyChi2SpectrumMultipole

namespace Omega.Zeta

noncomputable section

/-- The Rényi-2 closed form obtained from the chi-square multipole spectrum. -/
def xi_poisson_cauchy_renyi2_kl_upper_renyi2_closed_form
    {n : ℕ}
    (m : xi_poisson_cauchy_chi2_spectrum_multipole_positive_modes n) : ℝ :=
  Real.log (1 + xi_poisson_cauchy_chi2_spectrum_multipole_chi2_energy m)

/-- The corresponding nonasymptotic KL upper bound. -/
def xi_poisson_cauchy_renyi2_kl_upper_kl_upper_bound
    {n : ℕ}
    (m : xi_poisson_cauchy_chi2_spectrum_multipole_positive_modes n)
    (kl : ℝ) : Prop :=
  kl ≤ Real.log (1 + 2 * xi_poisson_cauchy_chi2_spectrum_multipole_positive_energy m)

/-- Paper label: `cor:xi-poisson-cauchy-renyi2-kl-upper`.
Using the finite chi-square multipole spectrum, the Rényi-2 expression rewrites as
`log (1 + 2 * positive energy)`, and any KL divergence bounded by Rényi-2 inherits
the same nonasymptotic bound. -/
theorem paper_xi_poisson_cauchy_renyi2_kl_upper
    (n : ℕ)
    (m : xi_poisson_cauchy_chi2_spectrum_multipole_positive_modes n)
    (kl : ℝ)
    (hkl : kl ≤ xi_poisson_cauchy_renyi2_kl_upper_renyi2_closed_form m) :
    xi_poisson_cauchy_renyi2_kl_upper_renyi2_closed_form m =
        Real.log
          (1 + 2 * xi_poisson_cauchy_chi2_spectrum_multipole_positive_energy m) ∧
      xi_poisson_cauchy_renyi2_kl_upper_kl_upper_bound m kl := by
  have hχ := paper_xi_poisson_cauchy_chi2_spectrum_multipole n m
  constructor
  · simp [xi_poisson_cauchy_renyi2_kl_upper_renyi2_closed_form, hχ]
  · simpa [xi_poisson_cauchy_renyi2_kl_upper_kl_upper_bound,
      xi_poisson_cauchy_renyi2_kl_upper_renyi2_closed_form, hχ] using hkl

end

end Omega.Zeta
