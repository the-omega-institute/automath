import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-collision-u1-audit-window-uniform-subcriticality`. If the slow mode is
`r` times the Perron scale and the ratio is uniformly bounded by the subcritical constant `q0`,
then every power of the slow mode is dominated by the corresponding exponential envelope. -/
theorem paper_xi_collision_u1_audit_window_uniform_subcriticality {I : Set ℝ}
    {r lambda slow : ℝ → ℝ} {q0 : ℝ} (hq0_pos : 0 < q0) (hq0_lt : q0 < 1)
    (hr_nonneg : ∀ u ∈ I, 0 ≤ r u) (hlambda_nonneg : ∀ u ∈ I, 0 ≤ lambda u)
    (hr_bound : ∀ u ∈ I, r u ≤ q0) (hslow : ∀ u ∈ I, slow u = r u * lambda u) :
    ∀ u ∈ I, ∀ n : ℕ, slow u ^ n ≤ q0 ^ n * lambda u ^ n := by
  intro u hu n
  have _hq0_window : 0 < q0 ∧ q0 < 1 := ⟨hq0_pos, hq0_lt⟩
  have hrpow : r u ^ n ≤ q0 ^ n :=
    pow_le_pow_left₀ (hr_nonneg u hu) (hr_bound u hu) n
  have hlampow : 0 ≤ lambda u ^ n := pow_nonneg (hlambda_nonneg u hu) n
  rw [hslow u hu, mul_pow]
  exact mul_le_mul_of_nonneg_right hrpow hlampow

end Omega.Zeta
