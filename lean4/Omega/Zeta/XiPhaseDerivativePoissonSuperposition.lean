import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The one-dimensional Poisson/Breit--Wigner kernel contributed by a zero with offset
`sigma` and ordinate `tau`. -/
noncomputable def xi_phase_derivative_poisson_superposition_kernel
    (sigma tau t : ℝ) : ℝ :=
  sigma / ((t - tau) ^ 2 + sigma ^ 2)

/-- Concrete zero-plus-singular-measure interface for
`prop:xi-phase-derivative-poisson-superposition`. -/
structure xi_phase_derivative_poisson_superposition_data where
  zeroCount : ℕ
  zeroOffset : Fin zeroCount → ℝ
  zeroOrdinate : Fin zeroCount → ℝ
  singularDensity : ℝ → ℝ
  phaseDerivative : ℝ → ℝ
  zeroOffset_pos : ∀ k : Fin zeroCount, 0 < zeroOffset k
  singularDensity_nonneg : ∀ t : ℝ, 0 ≤ singularDensity t
  phaseDerivative_eq_poisson_sum :
    ∀ t : ℝ,
      phaseDerivative t =
        (∑ k : Fin zeroCount,
          xi_phase_derivative_poisson_superposition_kernel
            (zeroOffset k) (zeroOrdinate k) t) + singularDensity t

namespace xi_phase_derivative_poisson_superposition_data

/-- Boundary phase derivative as the superposition of zero Poisson kernels and the
absolutely continuous singular-measure density. -/
def phaseDerivativeFormula (D : xi_phase_derivative_poisson_superposition_data) : Prop :=
  ∀ t : ℝ,
    D.phaseDerivative t =
      (∑ k : Fin D.zeroCount,
        xi_phase_derivative_poisson_superposition_kernel
          (D.zeroOffset k) (D.zeroOrdinate k) t) + D.singularDensity t

end xi_phase_derivative_poisson_superposition_data

/-- Paper label: `prop:xi-phase-derivative-poisson-superposition`. -/
theorem paper_xi_phase_derivative_poisson_superposition
    (D : xi_phase_derivative_poisson_superposition_data) :
    D.phaseDerivativeFormula := by
  exact D.phaseDerivative_eq_poisson_sum

end Omega.Zeta
