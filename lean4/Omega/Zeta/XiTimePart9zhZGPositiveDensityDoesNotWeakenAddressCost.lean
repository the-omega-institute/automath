import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9zh-zg-positive-density-does-not-weaken-address-cost`.
The corollary packages the address-cost lower bound together with the positive-density range of
the ZG admissible set. -/
theorem paper_xi_time_part9zh_zg_positive_density_does_not_weaken_address_cost
    (cost : ℕ → ℝ) (densityZG : ℝ)
    (hcost :
      ∃ c : ℝ, 0 < c ∧ ∃ T0 : ℕ, ∀ T ≥ T0,
        c * (T : ℝ) * Real.log (T : ℝ) ≤ cost T)
    (hdensity : 0 < densityZG ∧ densityZG < 1) :
    (∃ c : ℝ, 0 < c ∧ ∃ T0 : ℕ, ∀ T ≥ T0,
        c * (T : ℝ) * Real.log (T : ℝ) ≤ cost T) ∧
      0 < densityZG ∧ densityZG < 1 := by
  exact ⟨hcost, hdensity.1, hdensity.2⟩

end Omega.Zeta
