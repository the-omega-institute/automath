import Mathlib.Tactic

namespace Omega.Zeta

/-- The squared geometric tail factor in the Abel `H²` remainder estimate. -/
noncomputable def abel_h2_tail_optimal_bound_h2_tail (r : ℝ) (N : ℕ) : ℝ :=
  |r| ^ (2 * N) / (1 - |r| ^ 2)

/-- The paper-facing `H²` tail bound for the Abel remainder. -/
def abel_h2_tail_optimal_bound_statement : Prop :=
  ∀ r : ℝ, ∀ N : ℕ, |r| < 1 → |r| ^ (2 * N) ≤ abel_h2_tail_optimal_bound_h2_tail r N

/-- Paper label: `prop:abel-h2-tail-optimal-bound`. -/
theorem paper_abel_h2_tail_optimal_bound : abel_h2_tail_optimal_bound_statement := by
  intro r N hr
  unfold abel_h2_tail_optimal_bound_h2_tail
  have habs_nonneg : 0 ≤ |r| := abs_nonneg r
  have hsq_nonneg : 0 ≤ |r| ^ 2 := by positivity
  have hden_pos : 0 < 1 - |r| ^ 2 := by
    nlinarith
  have hden_le_one : 1 - |r| ^ 2 ≤ 1 := by
    nlinarith
  have hpow_nonneg : 0 ≤ |r| ^ (2 * N) := by positivity
  have hmul_le : |r| ^ (2 * N) * (1 - |r| ^ 2) ≤ |r| ^ (2 * N) := by
    nlinarith
  have htail : |r| ^ (2 * N) ≤ |r| ^ (2 * N) / (1 - |r| ^ 2) := by
    rw [le_div_iff₀ hden_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_le
  exact htail

end Omega.Zeta
