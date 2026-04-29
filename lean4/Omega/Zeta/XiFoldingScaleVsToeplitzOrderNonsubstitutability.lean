import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-folding-scale-vs-toeplitz-order-nonsubstitutability`. A product
budget bounds each reciprocal tradeoff after dividing by the positive resource on the other
axis. -/
theorem paper_xi_folding_scale_vs_toeplitz_order_nonsubstitutability {m N Q : ℝ}
    (hm : 0 < m) (hN : 0 < N) (hQ : Q ≤ m * N) : Q / m ≤ N ∧ Q / N ≤ m := by
  constructor
  · rw [div_le_iff₀ hm]
    nlinarith [hQ]
  · rw [div_le_iff₀ hN]
    nlinarith [hQ]

end Omega.Zeta
