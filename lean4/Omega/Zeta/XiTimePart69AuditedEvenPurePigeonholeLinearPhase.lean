import Mathlib

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-time-part69-audited-even-pure-pigeonhole-linear-phase`.
The audited even windows are indexed by the Fibonacci visible count. -/
def xi_time_part69_audited_even_pure_pigeonhole_linear_phase_visible_count
    (m : ℕ) : ℕ :=
  Nat.fib (m + 1)

/-- Paper label: `thm:xi-time-part69-audited-even-pure-pigeonhole-linear-phase`.
The finite set of visible audited windows. -/
def xi_time_part69_audited_even_pure_pigeonhole_linear_phase_windows
    (m : ℕ) : Finset ℕ :=
  Finset.range (xi_time_part69_audited_even_pure_pigeonhole_linear_phase_visible_count m)

/-- Paper label: `thm:xi-time-part69-audited-even-pure-pigeonhole-linear-phase`.
The low-budget capacity sum after capping each degeneracy by the pure budget `2^B`. -/
def xi_time_part69_audited_even_pure_pigeonhole_linear_phase_capacity_sum
    (B m : ℕ) (degeneracy : ℕ → ℕ) : ℕ :=
  ∑ x ∈ xi_time_part69_audited_even_pure_pigeonhole_linear_phase_windows m,
    min (degeneracy x) (2 ^ B)

/-- Paper label: `thm:xi-time-part69-audited-even-pure-pigeonhole-linear-phase`.
If every visible window has degeneracy at least `2^B`, every minimum is the budget and
the audited capacity is the Fibonacci visible count times `2^B`. -/
def xi_time_part69_audited_even_pure_pigeonhole_linear_phase_statement : Prop :=
  ∀ (B m : ℕ) (degeneracy : ℕ → ℕ),
    (∀ x ∈ xi_time_part69_audited_even_pure_pigeonhole_linear_phase_windows m,
      2 ^ B ≤ degeneracy x) →
      xi_time_part69_audited_even_pure_pigeonhole_linear_phase_capacity_sum
        B m degeneracy =
        xi_time_part69_audited_even_pure_pigeonhole_linear_phase_visible_count m * 2 ^ B

/-- Paper label: `thm:xi-time-part69-audited-even-pure-pigeonhole-linear-phase`. -/
theorem paper_xi_time_part69_audited_even_pure_pigeonhole_linear_phase :
    xi_time_part69_audited_even_pure_pigeonhole_linear_phase_statement := by
  intro B m degeneracy hthreshold
  calc
    xi_time_part69_audited_even_pure_pigeonhole_linear_phase_capacity_sum B m degeneracy
        = ∑ x ∈ xi_time_part69_audited_even_pure_pigeonhole_linear_phase_windows m,
            2 ^ B := by
          unfold xi_time_part69_audited_even_pure_pigeonhole_linear_phase_capacity_sum
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact min_eq_right (hthreshold x hx)
    _ = (xi_time_part69_audited_even_pure_pigeonhole_linear_phase_windows m).card * 2 ^ B := by
          simp
    _ = xi_time_part69_audited_even_pure_pigeonhole_linear_phase_visible_count m * 2 ^ B := by
          simp [xi_time_part69_audited_even_pure_pigeonhole_linear_phase_windows]

end Omega.Zeta
