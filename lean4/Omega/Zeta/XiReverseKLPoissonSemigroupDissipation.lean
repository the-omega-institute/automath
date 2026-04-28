import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the reverse-KL Poisson semigroup dissipation identity.

The fields record the smoothed density, entropy derivative, dissipation functional,
Fourier multiplier identity, nonnegativity, and zero-dissipation rigidity hypotheses
used by the paper theorem. -/
structure xi_reversekl_poisson_semigroup_dissipation_data where
  xi_reversekl_poisson_semigroup_dissipation_density : ℝ → ℝ → ℝ
  xi_reversekl_poisson_semigroup_dissipation_referenceDensity : ℝ → ℝ
  xi_reversekl_poisson_semigroup_dissipation_entropy : ℝ → ℝ
  xi_reversekl_poisson_semigroup_dissipation_entropyDerivative : ℝ → ℝ
  xi_reversekl_poisson_semigroup_dissipation_dissipation : ℝ → ℝ
  xi_reversekl_poisson_semigroup_dissipation_fourierMultiplier :
    ∀ t : ℝ, 0 < t →
      xi_reversekl_poisson_semigroup_dissipation_entropyDerivative t =
        -xi_reversekl_poisson_semigroup_dissipation_dissipation t
  xi_reversekl_poisson_semigroup_dissipation_nonnegative :
    ∀ t : ℝ, 0 < t → 0 ≤ xi_reversekl_poisson_semigroup_dissipation_dissipation t
  xi_reversekl_poisson_semigroup_dissipation_zeroRigidity :
    ∀ t : ℝ, 0 < t →
      xi_reversekl_poisson_semigroup_dissipation_dissipation t = 0 →
        (∀ θ : ℝ, xi_reversekl_poisson_semigroup_dissipation_density t θ = 1) ∧
          ∀ θ : ℝ, xi_reversekl_poisson_semigroup_dissipation_referenceDensity θ = 1

namespace xi_reversekl_poisson_semigroup_dissipation_data

/-- The identity and rigidity conclusion supplied by the concrete Poisson semigroup data. -/
def identity_and_rigidity (D : xi_reversekl_poisson_semigroup_dissipation_data) : Prop :=
  (∀ t : ℝ, 0 < t →
    D.xi_reversekl_poisson_semigroup_dissipation_entropyDerivative t =
      -D.xi_reversekl_poisson_semigroup_dissipation_dissipation t ∧
    0 ≤ D.xi_reversekl_poisson_semigroup_dissipation_dissipation t) ∧
  ∀ t : ℝ, 0 < t →
    D.xi_reversekl_poisson_semigroup_dissipation_dissipation t = 0 →
      (∀ θ : ℝ, D.xi_reversekl_poisson_semigroup_dissipation_density t θ = 1) ∧
        ∀ θ : ℝ, D.xi_reversekl_poisson_semigroup_dissipation_referenceDensity θ = 1

end xi_reversekl_poisson_semigroup_dissipation_data

/-- Poisson semigroup reverse-KL dissipation identity and zero-dissipation rigidity.
    thm:xi-reversekl-poisson-semigroup-dissipation -/
theorem paper_xi_reversekl_poisson_semigroup_dissipation
    (D : xi_reversekl_poisson_semigroup_dissipation_data) :
    D.identity_and_rigidity := by
  constructor
  · intro t ht
    exact ⟨D.xi_reversekl_poisson_semigroup_dissipation_fourierMultiplier t ht,
      D.xi_reversekl_poisson_semigroup_dissipation_nonnegative t ht⟩
  · intro t ht hzero
    exact D.xi_reversekl_poisson_semigroup_dissipation_zeroRigidity t ht hzero

end Omega.Zeta
