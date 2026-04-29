import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Kronecker

noncomputable section

/-- Even Fibonacci-subsequence limit of the normalized W1 transport certificate. -/
def xi_golden_fibonacci_star_w1_oscillation_cesaro_transport_even : ℝ :=
  (1 / 2 : ℝ) + 1 / (2 * Real.sqrt 5)

/-- Odd Fibonacci-subsequence limit of the normalized W1 transport certificate. -/
def xi_golden_fibonacci_star_w1_oscillation_cesaro_transport_odd : ℝ :=
  (1 / 2 : ℝ) - 1 / (2 * Real.sqrt 5) + 1 / 15

/-- Even Fibonacci-subsequence limit of the normalized star discrepancy certificate. -/
def xi_golden_fibonacci_star_w1_oscillation_cesaro_star_even : ℝ :=
  1 + 1 / Real.sqrt 5

/-- Odd Fibonacci-subsequence limit of the normalized star discrepancy certificate. -/
def xi_golden_fibonacci_star_w1_oscillation_cesaro_star_odd : ℝ :=
  1

/-- Exact parity profile abstracting the isolated even/odd Fibonacci subsequential limits. -/
def xi_golden_fibonacci_star_w1_oscillation_cesaro_parityProfile
    (D T : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, T (2 * n) =
      xi_golden_fibonacci_star_w1_oscillation_cesaro_transport_even) ∧
    (∀ n : ℕ, T (2 * n + 1) =
      xi_golden_fibonacci_star_w1_oscillation_cesaro_transport_odd) ∧
    (∀ n : ℕ, D (2 * n) =
      xi_golden_fibonacci_star_w1_oscillation_cesaro_star_even) ∧
    ∀ n : ℕ, D (2 * n + 1) =
      xi_golden_fibonacci_star_w1_oscillation_cesaro_star_odd

/-- One-period oscillation amplitude of an exact parity profile. -/
def xi_golden_fibonacci_star_w1_oscillation_cesaro_amplitude (a : ℕ → ℝ) : ℝ :=
  a 0 - a 1

/-- One-period Cesaro value for an exact parity profile, using the density `1/2` of each parity. -/
def xi_golden_fibonacci_star_w1_oscillation_cesaro_pairAverage (a : ℕ → ℝ) : ℝ :=
  (a 0 + a 1) / 2

/-- Paper label: `cor:xi-golden-fibonacci-star-w1-oscillation-cesaro`. -/
theorem paper_xi_golden_fibonacci_star_w1_oscillation_cesaro (D T : ℕ → ℝ) :
    xi_golden_fibonacci_star_w1_oscillation_cesaro_parityProfile D T →
      xi_golden_fibonacci_star_w1_oscillation_cesaro_amplitude T =
          1 / Real.sqrt 5 - 1 / 15 ∧
        xi_golden_fibonacci_star_w1_oscillation_cesaro_amplitude D =
          1 / Real.sqrt 5 ∧
        xi_golden_fibonacci_star_w1_oscillation_cesaro_pairAverage T = 8 / 15 ∧
        xi_golden_fibonacci_star_w1_oscillation_cesaro_pairAverage D =
          1 + 1 / (2 * Real.sqrt 5) := by
  intro hprofile
  rcases hprofile with ⟨hTeven, hTodd, hDeven, hDodd⟩
  have hT0 := hTeven 0
  have hT1 := hTodd 0
  have hD0 := hDeven 0
  have hD1 := hDodd 0
  norm_num at hT0 hT1 hD0 hD1
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold xi_golden_fibonacci_star_w1_oscillation_cesaro_amplitude
    rw [hT0, hT1]
    unfold xi_golden_fibonacci_star_w1_oscillation_cesaro_transport_even
      xi_golden_fibonacci_star_w1_oscillation_cesaro_transport_odd
    ring
  · unfold xi_golden_fibonacci_star_w1_oscillation_cesaro_amplitude
    rw [hD0, hD1]
    unfold xi_golden_fibonacci_star_w1_oscillation_cesaro_star_even
      xi_golden_fibonacci_star_w1_oscillation_cesaro_star_odd
    ring
  · unfold xi_golden_fibonacci_star_w1_oscillation_cesaro_pairAverage
    rw [hT0, hT1]
    unfold xi_golden_fibonacci_star_w1_oscillation_cesaro_transport_even
      xi_golden_fibonacci_star_w1_oscillation_cesaro_transport_odd
    ring
  · unfold xi_golden_fibonacci_star_w1_oscillation_cesaro_pairAverage
    rw [hD0, hD1]
    unfold xi_golden_fibonacci_star_w1_oscillation_cesaro_star_even
      xi_golden_fibonacci_star_w1_oscillation_cesaro_star_odd
    ring

end

end Omega.Kronecker
