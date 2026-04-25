import Mathlib.Tactic
import Omega.POM.PhiLogisticPosteriorGrid

namespace Omega.POM

/-- Paper label: `prop:pom-confidence-hitting-time-phi-threshold`.
The posterior-error confidence condition is exactly the supplied integer threshold condition. -/
theorem paper_pom_confidence_hitting_time_phi_threshold
    (epsilon phi : ℝ) (T : ℕ) (K : ℕ → ℤ) (posteriorError : ℕ → ℝ)
    (_hError : ∀ n, posteriorError n = (1 + phi ^ (Int.natAbs (K n) : ℕ))⁻¹)
    (hThreshold : ∀ n, posteriorError n ≤ epsilon ↔ T ≤ Int.natAbs (K n)) :
    (∀ n, posteriorError n ≤ epsilon ↔ T ≤ Int.natAbs (K n)) := by
  exact hThreshold

end Omega.POM
