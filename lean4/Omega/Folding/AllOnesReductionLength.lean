import Mathlib.Tactic

namespace Omega.Folding

private lemma nat_square_div_four_step (m : ℕ) : (m + 2) ^ 2 / 4 = m ^ 2 / 4 + (m + 1) := by
  calc
    (m + 2) ^ 2 / 4 = (m ^ 2 + (m + 1) * 4) / 4 := by
      congr 1
      ring
    _ = m ^ 2 / 4 + (m + 1) := by
      rw [Nat.add_mul_div_right _ _ (by positivity)]

set_option maxHeartbeats 400000 in
/-- Closed form for the reduction length recurrence on the all-ones input. -/
theorem paper_all_ones_reduction_length (T : ℕ → ℕ) (h1 : T 1 = 0) (h2 : T 2 = 1)
    (hrec : ∀ m ≥ 3, T m = T (m - 2) + (m - 1)) : ∀ m ≥ 1, T m = m ^ 2 / 4 := by
  have hclosed : ∀ k : ℕ, T (k + 1) = (k + 1) ^ 2 / 4 := by
    refine Nat.twoStepInduction ?_ ?_ ?_
    · simpa using h1
    · simpa using h2
    · intro k hk hk1
      have hstep : T (k + 3) = T ((k + 3) - 2) + ((k + 3) - 1) := by
        exact hrec (k + 3) (by omega)
      calc
        T (k + 3) = T (k + 1) + (k + 2) := by simpa using hstep
        _ = (k + 1) ^ 2 / 4 + (k + 2) := by rw [hk]
        _ = (k + 3) ^ 2 / 4 := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (nat_square_div_four_step (k + 1)).symm
  intro m hm
  cases m with
  | zero =>
      omega
  | succ k =>
      simpa using hclosed k

end Omega.Folding
