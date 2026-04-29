import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9o-periodic-ripple-diffusive-lifetime`. -/
theorem paper_xi_time_part9o_periodic_ripple_diffusive_lifetime
    (L R : ℕ → ℝ) (C E K : ℝ) (hE : 0 ≤ E) (hK : 0 ≤ K)
    (hasymp : ∀ p, 3 ≤ p → |L p - (C * (p : ℝ)^2 + R p)| ≤ E)
    (hR : ∀ p, 3 ≤ p → |R p| ≤ K) :
    ∀ p, 3 ≤ p → |L p - C * (p : ℝ)^2| ≤ E + K := by
  have _ : 0 ≤ E + K := add_nonneg hE hK
  intro p hp
  have hmain := hasymp p hp
  have hrem := hR p hp
  have hsplit :
      L p - C * (p : ℝ)^2 = (L p - (C * (p : ℝ)^2 + R p)) + R p := by
    ring
  calc
    |L p - C * (p : ℝ)^2|
        = |(L p - (C * (p : ℝ)^2 + R p)) + R p| := by rw [hsplit]
    _ ≤ |L p - (C * (p : ℝ)^2 + R p)| + |R p| := abs_add_le _ _
    _ ≤ E + K := add_le_add hmain hrem

end Omega.Zeta
