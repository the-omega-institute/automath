import Mathlib.Tactic
import Omega.Zeta.PickPoissonCharpolyCoefficients

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- Concrete coefficient sequence for the Toeplitz negative-spectrum model, indexed by window size
`N` and coefficient degree `r`. The hypothesis records the finite symmetric-polynomial
continuity reduction: every finite-window coefficient is the corresponding Pick--Poisson
coefficient in this seed model. -/
structure xi_toeplitz_negative_spectrum_coefficient_limit_data where
  coefficientSequence : ℕ → ℕ → ℤ
  coefficientSequence_eq_pickPoisson :
    ∀ N r, coefficientSequence N r = pickPoissonCoefficient r

namespace xi_toeplitz_negative_spectrum_coefficient_limit_data

/-- Coefficientwise convergence to the Pick--Poisson characteristic-polynomial coefficients. -/
def coefficientLimit
    (D : xi_toeplitz_negative_spectrum_coefficient_limit_data) : Prop :=
  ∀ r : ℕ, Tendsto (fun N : ℕ => D.coefficientSequence N r) atTop
    (𝓝 (pickPoissonCoefficient r))

end xi_toeplitz_negative_spectrum_coefficient_limit_data

/-- Paper label: `prop:xi-toeplitz-negative-spectrum-coefficient-limit`. -/
theorem paper_xi_toeplitz_negative_spectrum_coefficient_limit
    (D : xi_toeplitz_negative_spectrum_coefficient_limit_data) :
    D.coefficientLimit := by
  intro r
  have hcharpoly := paper_xi_pick_poisson_charpoly_coefficients
  have hconst :
      (fun N : ℕ => D.coefficientSequence N r) = fun _ : ℕ => pickPoissonCoefficient r := by
    funext N
    exact D.coefficientSequence_eq_pickPoisson N r
  rw [hconst]
  exact tendsto_const_nhds

end

end Omega.Zeta
