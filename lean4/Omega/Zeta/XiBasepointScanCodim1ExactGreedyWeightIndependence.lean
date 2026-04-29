import Mathlib

namespace Omega.Zeta

/-- Paper label: `thm:xi-basepoint-scan-codim1-exact-greedy-weight-independence`. -/
theorem paper_xi_basepoint_scan_codim1_exact_greedy_weight_independence {ι : Type*}
    (objective : (ι → ℝ) → ℝ → ℝ) (shape : ℝ → ℝ) (scale : (ι → ℝ) → ℝ)
    (hscale_pos : ∀ w, 0 < scale w)
    (hfactor : ∀ w x, objective w x = scale w * shape x) :
    ∀ w1 w2 x,
      (∀ y, objective w1 y ≤ objective w1 x) ↔
        (∀ y, objective w2 y ≤ objective w2 x) := by
  intro w1 w2 x
  constructor
  · intro h y
    have hy_shape : shape y ≤ shape x := by
      have hy := h y
      rw [hfactor w1 y, hfactor w1 x] at hy
      exact le_of_mul_le_mul_left hy (hscale_pos w1)
    rw [hfactor w2 y, hfactor w2 x]
    exact mul_le_mul_of_nonneg_left hy_shape (le_of_lt (hscale_pos w2))
  · intro h y
    have hy_shape : shape y ≤ shape x := by
      have hy := h y
      rw [hfactor w2 y, hfactor w2 x] at hy
      exact le_of_mul_le_mul_left hy (hscale_pos w2)
    rw [hfactor w1 y, hfactor w1 x]
    exact mul_le_mul_of_nonneg_left hy_shape (le_of_lt (hscale_pos w1))

end Omega.Zeta
