import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-scan-two-source-stability-gap`. -/
theorem paper_xi_scan_two_source_stability_gap {rho1 rho2 c1 c2 Delta : ℝ}
    (hrho : 0 < rho2 ∧ rho2 < rho1) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hDelta : c1 * c2 * (rho1 - rho2) ^ 2 ≤ Delta) :
    rho1 - rho2 ≤ Real.sqrt (Delta / (c1 * c2)) := by
  rcases hrho with ⟨_, hrho21⟩
  have hgap_nonneg : 0 ≤ rho1 - rho2 := by linarith
  have hden_pos : 0 < c1 * c2 := mul_pos hc1 hc2
  have hsq_le : (rho1 - rho2) ^ 2 ≤ Delta / (c1 * c2) := by
    exact (le_div_iff₀ hden_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hDelta)
  simpa [Real.sqrt_sq hgap_nonneg] using Real.sqrt_le_sqrt hsq_le

end Omega.Zeta
