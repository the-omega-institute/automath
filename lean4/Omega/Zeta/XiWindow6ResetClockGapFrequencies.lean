import Mathlib.Tactic

namespace Omega.Zeta

/-- The count of `55`-gaps after `n` Fibonacci-substitution steps. -/
abbrev xi_window6_reset_clock_gap_frequencies_count55 (n : ℕ) : ℕ :=
  Nat.fib (n + 1)

/-- The count of `34`-gaps after `n` Fibonacci-substitution steps. -/
abbrev xi_window6_reset_clock_gap_frequencies_count34 (n : ℕ) : ℕ :=
  Nat.fib n

lemma xi_window6_reset_clock_gap_frequencies_recurrence (n : ℕ) :
    xi_window6_reset_clock_gap_frequencies_count55 (n + 1) =
        xi_window6_reset_clock_gap_frequencies_count55 n +
          xi_window6_reset_clock_gap_frequencies_count34 n ∧
      xi_window6_reset_clock_gap_frequencies_count34 (n + 1) =
        xi_window6_reset_clock_gap_frequencies_count55 n := by
  constructor
  · dsimp [xi_window6_reset_clock_gap_frequencies_count55,
      xi_window6_reset_clock_gap_frequencies_count34]
    rw [show n + 1 + 1 = n + 2 by omega]
    rw [Nat.fib_add_two]
    exact Nat.add_comm _ _
  · rfl

lemma xi_window6_reset_clock_gap_frequencies_closed_counts (n : ℕ) :
    xi_window6_reset_clock_gap_frequencies_count55 n = Nat.fib (n + 1) ∧
      xi_window6_reset_clock_gap_frequencies_count34 n = Nat.fib n := by
  exact ⟨rfl, rfl⟩

/-- Paper label: `cor:xi-window6-reset-clock-gap-frequencies`. -/
theorem paper_xi_window6_reset_clock_gap_frequencies :
    ∃ count55 count34 : ℕ → ℕ,
      count55 0 = 1 ∧ count34 0 = 0 ∧
        (∀ n,
          count55 (n + 1) = count55 n + count34 n ∧
            count34 (n + 1) = count55 n) ∧
          (∀ n, count55 n = Nat.fib (n + 1) ∧ count34 n = Nat.fib n) := by
  refine ⟨xi_window6_reset_clock_gap_frequencies_count55,
    xi_window6_reset_clock_gap_frequencies_count34, ?_, ?_, ?_, ?_⟩
  · norm_num [xi_window6_reset_clock_gap_frequencies_count55, Nat.fib]
  · rfl
  · exact xi_window6_reset_clock_gap_frequencies_recurrence
  · exact xi_window6_reset_clock_gap_frequencies_closed_counts

end Omega.Zeta
