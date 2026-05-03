import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-basepoint-scan-leverage-gap-codim1-critical-points`.

If the logarithmic derivative is twice a balance functional, every critical point of the
logarithmic derivative forces the weight-independent balance equation. -/
theorem paper_xi_basepoint_scan_leverage_gap_codim1_critical_points
    (logDeriv balance : ℝ → ℝ) (critical : ℝ → Prop)
    (hcrit : ∀ x, critical x → logDeriv x = 0)
    (hbalance : ∀ x, logDeriv x = 2 * balance x) :
    ∀ x, critical x → balance x = 0 := by
  intro x hx
  have hzero : 2 * balance x = 0 := by
    simpa [hbalance x] using hcrit x hx
  linarith

end Omega.Zeta
