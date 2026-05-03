import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-endpoint-poisson-cauchy-cayley-pullback`. -/
theorem paper_xi_endpoint_poisson_cauchy_cayley_pullback (r t : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) :
    ((1 - r ^ 2) / (((1 + r) ^ 2 + (1 - r) ^ 2 * t ^ 2) / (1 + t ^ 2))) *
          (2 / (1 + t ^ 2)) / (2 * Real.pi) =
        (1 / Real.pi) *
          (((1 + r) / (1 - r)) / (t ^ 2 + ((1 + r) / (1 - r)) ^ 2)) := by
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  have hrden : 1 - r ≠ 0 := by linarith
  have hscale : (1 + r) / (1 - r) ≠ 0 := by
    positivity
  have hquad : (1 + r) ^ 2 + (1 - r) ^ 2 * t ^ 2 ≠ 0 := by
    positivity
  have hcauchy : t ^ 2 + ((1 + r) / (1 - r)) ^ 2 ≠ 0 := by
    positivity
  field_simp [Real.pi_ne_zero, ht, hrden, hscale, hquad, hcauchy]
  ring

end Omega.Zeta
