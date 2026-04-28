import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zb-foldpi-two-atomic-moment-characterization`. -/
theorem paper_xi_time_part9zb_foldpi_two_atomic_moment_characterization
    (a b x y : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0) (hxy : x ≠ y)
    (f : ℕ → ℝ) (hf : ∀ k : ℕ, f k = a * x ^ k + b * y ^ k) :
    (∀ k : ℕ, f (k + 2) = (x + y) * f (k + 1) - (x * y) * f k) ∧
      f 1 * f 3 - f 2 * f 2 = a * b * x * y * (y - x) ^ 2 := by
  have hnondegenerate : a ≠ 0 ∧ b ≠ 0 ∧ x ≠ 0 ∧ x ≠ y := ⟨ha, hb, hx, hxy⟩
  clear hnondegenerate
  constructor
  · intro k
    rw [hf (k + 2), hf (k + 1), hf k]
    ring_nf
  · rw [hf 1, hf 2, hf 3]
    ring

end Omega.Zeta
