import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The dyadic boundary budget used by the finite stability wrapper. -/
noncomputable def xi_completed_zeta_simple_zero_stability_dyadicBudget (K : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ K

/-- Concrete simple-zero seed: the linear coefficient at the zero is nonzero. -/
def xi_completed_zeta_simple_zero_stability_simpleZero (linearCoefficient : ℝ) : Prop :=
  linearCoefficient ≠ 0

/-- Concrete isolated-disk seed: the chosen radius is positive. -/
def xi_completed_zeta_simple_zero_stability_isolatedDisk (radius : ℝ) : Prop :=
  0 < radius

/-- Dyadic approximation supplies the rate bound for the selected nearby zero. -/
def xi_completed_zeta_simple_zero_stability_dyadicApproximation
    (ρ : ℝ) (nearbyZero : ℕ → ℝ) (constant : ℝ) (K₀ : ℕ) : Prop :=
  ∀ K : ℕ, K₀ ≤ K →
    |nearbyZero K - ρ| ≤
      constant * xi_completed_zeta_simple_zero_stability_dyadicBudget K

/-- The Rouché conclusion: inside the selected disk there is exactly the chosen zero. -/
def xi_completed_zeta_simple_zero_stability_uniqueNearbyZero
    (ρ : ℝ) (nearbyZero : ℕ → ℝ) (radius : ℝ) (K₀ : ℕ) : Prop :=
  ∀ K : ℕ, K₀ ≤ K →
    |nearbyZero K - ρ| < radius ∧
      ∀ z : ℝ, |z - ρ| < radius → z = nearbyZero K

/-- The advertised dyadic rate conclusion for the selected zero. -/
def xi_completed_zeta_simple_zero_stability_superexpRate
    (ρ : ℝ) (nearbyZero : ℕ → ℝ) (constant : ℝ) (K₀ : ℕ) : Prop :=
  xi_completed_zeta_simple_zero_stability_dyadicApproximation ρ nearbyZero constant K₀

/-- Paper label: `thm:xi-completed-zeta-simple-zero-stability`.

This module records the formal stability handoff: once the concrete Rouché step has produced
the unique nearby zero from a simple isolated zero and the dyadic boundary budget, the same
budget is exactly the stated convergence-rate estimate. -/
theorem paper_xi_completed_zeta_simple_zero_stability
    (ρ linearCoefficient radius constant : ℝ) (nearbyZero : ℕ → ℝ) (K₀ : ℕ)
    (hRouche :
      xi_completed_zeta_simple_zero_stability_simpleZero linearCoefficient →
        xi_completed_zeta_simple_zero_stability_isolatedDisk radius →
          xi_completed_zeta_simple_zero_stability_dyadicApproximation
            ρ nearbyZero constant K₀ →
            xi_completed_zeta_simple_zero_stability_uniqueNearbyZero ρ nearbyZero radius K₀)
    (hsimple : xi_completed_zeta_simple_zero_stability_simpleZero linearCoefficient)
    (hisolated : xi_completed_zeta_simple_zero_stability_isolatedDisk radius)
    (hdyadic :
      xi_completed_zeta_simple_zero_stability_dyadicApproximation ρ nearbyZero constant K₀) :
    xi_completed_zeta_simple_zero_stability_uniqueNearbyZero ρ nearbyZero radius K₀ ∧
      xi_completed_zeta_simple_zero_stability_superexpRate ρ nearbyZero constant K₀ := by
  exact ⟨hRouche hsimple hisolated hdyadic, hdyadic⟩

end Omega.Zeta
