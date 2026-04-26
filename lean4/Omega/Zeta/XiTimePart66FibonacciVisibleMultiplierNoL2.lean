import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part66-fibonacci-visible-multiplier-no-l2`. If two
coefficient streams are eventually bounded away from zero, then the squared product
coefficients cannot be summable. -/
theorem paper_xi_time_part66_fibonacci_visible_multiplier_no_l2 (a b : ℕ → ℝ) (c d : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (ha : Filter.Eventually (fun n : ℕ => c ≤ |a n|) Filter.atTop)
    (hb : Filter.Eventually (fun n : ℕ => d ≤ |b n|) Filter.atTop) :
    ¬ Summable (fun n : ℕ => (a n * b n)^2) := by
  intro hs
  have hcd_pos : 0 < c * d := mul_pos hc hd
  have hcd_sq_pos : 0 < (c * d)^2 := sq_pos_of_pos hcd_pos
  have hbound : ∀ᶠ n : ℕ in Filter.atTop, (c * d)^2 ≤ (a n * b n)^2 := by
    filter_upwards [ha, hb] with n han hbn
    have hprod_abs : c * d ≤ |a n * b n| := by
      rw [abs_mul]
      exact mul_le_mul han hbn (le_of_lt hd) (abs_nonneg (a n))
    have hprod_sq : (c * d)^2 ≤ |a n * b n|^2 := by
      nlinarith [hprod_abs, abs_nonneg (a n * b n), le_of_lt hcd_pos]
    rw [← sq_abs (a n * b n)]
    exact hprod_sq
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, (a n * b n)^2 < (c * d)^2 :=
    hs.tendsto_atTop_zero.eventually_lt_const hcd_sq_pos
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hbound
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hsmall
  let N := max N₁ N₂
  have hle := hN₁ N (le_max_left N₁ N₂)
  have hlt := hN₂ N (le_max_right N₁ N₂)
  linarith

end Omega.Zeta
