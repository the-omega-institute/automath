import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Heat multiplier at time `s` and frequency `ξ`. -/
noncomputable def xi_poisson_subordination_half_stable_heat_multiplier (s ξ : ℝ) : ℝ :=
  Real.exp (-(s * ξ ^ 2))

/-- Poisson multiplier at scale `t` and frequency `ξ`. -/
noncomputable def xi_poisson_subordination_half_stable_poisson_multiplier (t ξ : ℝ) : ℝ :=
  Real.exp (-(t * |ξ|))

/-- Laplace transform characterizing the `1/2`-stable subordinator. -/
noncomputable def xi_poisson_subordination_half_stable_laplace_transform
    (t lam : ℝ) : ℝ :=
  Real.exp (-(t * Real.sqrt lam))

/-- The subordinated heat multiplier obtained by evaluating the Laplace transform at
`λ = ξ^2`. -/
noncomputable def xi_poisson_subordination_half_stable_subordinated_heat_multiplier
    (t ξ : ℝ) : ℝ :=
  xi_poisson_subordination_half_stable_laplace_transform t (ξ ^ 2)

/-- Paper label: `prop:xi-poisson-subordination-half-stable`.  The abstract subordination
package is recorded through its concrete Laplace-transform characterization; evaluating that
characterization at `λ = ξ^2` gives exactly the Poisson Fourier multiplier. -/
def xi_poisson_subordination_half_stable_statement : Prop :=
  (∀ t lam : ℝ, 0 < t → 0 ≤ lam →
      xi_poisson_subordination_half_stable_laplace_transform t lam =
        Real.exp (-(t * Real.sqrt lam))) ∧
    (∀ t ξ : ℝ, 0 < t →
      xi_poisson_subordination_half_stable_subordinated_heat_multiplier t ξ =
        xi_poisson_subordination_half_stable_poisson_multiplier t ξ) ∧
    (∀ L : ℝ → ℝ → ℝ,
      (∀ t lam : ℝ, 0 < t → 0 < lam →
        L t lam = xi_poisson_subordination_half_stable_laplace_transform t lam) →
        ∀ t lam : ℝ, 0 < t → 0 < lam →
          L t lam = Real.exp (-(t * Real.sqrt lam)))

theorem paper_xi_poisson_subordination_half_stable :
    xi_poisson_subordination_half_stable_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro t lam ht hlam
    rfl
  · intro t ξ ht
    unfold xi_poisson_subordination_half_stable_subordinated_heat_multiplier
      xi_poisson_subordination_half_stable_laplace_transform
      xi_poisson_subordination_half_stable_poisson_multiplier
    rw [Real.sqrt_sq_eq_abs]
  · intro L hL t lam ht hlam
    rw [hL t lam ht hlam]
    rfl

end

end Omega.Zeta
