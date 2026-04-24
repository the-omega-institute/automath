import Mathlib.Tactic

namespace Omega.POM

/-- Log-convex positive tails have decreasing hazard rates, since
`h_k = 1 - S_k / S_{k - 1}` and the ratio sequence is increasing. -/
theorem paper_pom_diagonal_rate_absorbing_dfr (S : ℕ → ℚ) (hpos : ∀ k, 0 < S k)
    (hlogconvex : ∀ k ≥ 1, S k ^ 2 ≤ S (k - 1) * S (k + 1)) :
    ∀ k ≥ 1, 1 - S (k + 1) / S k ≤ 1 - S k / S (k - 1) := by
  intro k hk
  have hkpos : 0 < S k := hpos k
  have hkm1pos : 0 < S (k - 1) := hpos (k - 1)
  have hratio : S k / S (k - 1) ≤ S (k + 1) / S k := by
    rw [div_le_div_iff₀ hkm1pos hkpos]
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hlogconvex k hk
  linarith

end Omega.POM
