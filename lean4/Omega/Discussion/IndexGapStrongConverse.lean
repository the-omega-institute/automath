import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Discussion

/-- Paper label: `con:discussion-index-gap-strong-converse`.

If the information budget `I n` dominates the linear gap lower bound `n * Γ` for every round,
but is also sublinear, then the gap constant must vanish. -/
theorem paper_discussion_index_gap_strong_converse
    (Γ : ℝ) (I : ℕ → ℝ) (hΓ_nonneg : 0 ≤ Γ) (hlower : ∀ n : ℕ, (n : ℝ) * Γ ≤ I n)
    (hsublinear : ∀ ε > 0, ∃ N, ∀ n : ℕ, n ≥ N → I n ≤ ε * (n : ℝ)) : Γ = 0 := by
  by_cases hΓ_zero : Γ = 0
  · exact hΓ_zero
  · have hΓ_pos : 0 < Γ := lt_of_le_of_ne hΓ_nonneg (Ne.symm hΓ_zero)
    rcases hsublinear (Γ / 2) (by linarith) with ⟨N, hN⟩
    have hlow := hlower (N + 1)
    have hupp := hN (N + 1) (Nat.le_succ N)
    have hnpos : (0 : ℝ) < (N + 1 : ℕ) := by
      exact_mod_cast Nat.succ_pos N
    have hscaled : ((N + 1 : ℕ) : ℝ) * Γ ≤ (Γ / 2) * ((N + 1 : ℕ) : ℝ) := by
      linarith
    have hscaled' : Γ * ((N + 1 : ℕ) : ℝ) ≤ (Γ / 2) * ((N + 1 : ℕ) : ℝ) := by
      simpa [mul_comm] using hscaled
    have hhalf : Γ ≤ Γ / 2 := by
      nlinarith [hscaled', hnpos]
    linarith

end Omega.Discussion
