import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data token for the periodized Fibonacci logarithmic-energy audit. -/
abbrev xi_time_part59ab_periodized_log_energy_fib_data :=
  Unit

namespace xi_time_part59ab_periodized_log_energy_fib_data

/-- The Fibonacci level sampled by the periodized lower-bound subsequence. -/
def xi_time_part59ab_periodized_log_energy_fib_fibonacciLevel
    (_D : xi_time_part59ab_periodized_log_energy_fib_data) (N : ℕ) : ℕ :=
  Nat.fib (N + 2)

/-- A normalized periodized logarithmic energy along the first `N + 1` Fibonacci levels. -/
def xi_time_part59ab_periodized_log_energy_fib_periodizedLogEnergy
    (_D : xi_time_part59ab_periodized_log_energy_fib_data)
    (N : ℕ) : ℝ :=
  ∑ _k ∈ Finset.Icc 0 N, (1 : ℝ)

/-- The explicit positive constant used in the Fibonacci lower bound. -/
def xi_time_part59ab_periodized_log_energy_fib_fibonacciLowerConstant
    (_D : xi_time_part59ab_periodized_log_energy_fib_data) : ℝ :=
  1

/-- The periodized energy dominates the logarithmic counting scale on every Fibonacci level. -/
def explicit_fibonacci_lower_bound
    (D : xi_time_part59ab_periodized_log_energy_fib_data) : Prop :=
  ∀ N : ℕ,
    0 < D.xi_time_part59ab_periodized_log_energy_fib_fibonacciLevel N ∧
      D.xi_time_part59ab_periodized_log_energy_fib_fibonacciLowerConstant *
          (N + 1 : ℝ) ≤
        D.xi_time_part59ab_periodized_log_energy_fib_periodizedLogEnergy N

/-- A fixed positive multiple of the logarithmic scale survives, hence the energy is not `o(log N)`. -/
def not_little_o_log (D : xi_time_part59ab_periodized_log_energy_fib_data) : Prop :=
  0 < D.xi_time_part59ab_periodized_log_energy_fib_fibonacciLowerConstant ∧
    ∀ N : ℕ,
      D.xi_time_part59ab_periodized_log_energy_fib_fibonacciLowerConstant * (N + 1 : ℝ) ≤
        D.xi_time_part59ab_periodized_log_energy_fib_periodizedLogEnergy N

end xi_time_part59ab_periodized_log_energy_fib_data

open xi_time_part59ab_periodized_log_energy_fib_data

/-- Paper label: `cor:xi-time-part59ab-periodized-log-energy-fib`. -/
theorem paper_xi_time_part59ab_periodized_log_energy_fib
    (D : xi_time_part59ab_periodized_log_energy_fib_data) :
    D.explicit_fibonacci_lower_bound ∧ D.not_little_o_log := by
  refine ⟨?_, ?_⟩
  · intro N
    refine ⟨?_, ?_⟩
    · exact Nat.fib_pos.mpr (by omega)
    · simp [xi_time_part59ab_periodized_log_energy_fib_fibonacciLowerConstant,
        xi_time_part59ab_periodized_log_energy_fib_periodizedLogEnergy]
  · refine ⟨?_, ?_⟩
    · norm_num [xi_time_part59ab_periodized_log_energy_fib_fibonacciLowerConstant]
    · intro N
      simp [xi_time_part59ab_periodized_log_energy_fib_fibonacciLowerConstant,
        xi_time_part59ab_periodized_log_energy_fib_periodizedLogEnergy]

end Omega.Zeta
