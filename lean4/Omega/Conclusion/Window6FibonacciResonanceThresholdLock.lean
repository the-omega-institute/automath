import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The lower window-6 phase band below the first Fibonacci threshold. -/
def conclusion_window6_fibonacci_resonance_threshold_lock_lowBand : Finset ℕ :=
  Finset.Icc 0 7

/-- The middle window-6 phase band between the two Fibonacci thresholds. -/
def conclusion_window6_fibonacci_resonance_threshold_lock_midBand : Finset ℕ :=
  Finset.Icc 8 12

/-- The upper window-6 phase band above the second Fibonacci threshold inside `Z / 21 Z`. -/
def conclusion_window6_fibonacci_resonance_threshold_lock_highBand : Finset ℕ :=
  Finset.Icc 13 20

/-- Concrete window-6 Fibonacci threshold and interval-partition statement. -/
def conclusion_window6_fibonacci_resonance_threshold_lock_statement : Prop :=
  Nat.fib 6 = 8 ∧
    Nat.fib 7 = 13 ∧
    Nat.fib 8 = 21 ∧
    (∀ n : ℕ, n < Nat.fib 8 →
      (n ∈ conclusion_window6_fibonacci_resonance_threshold_lock_lowBand ↔ n < Nat.fib 6) ∧
        (n ∈ conclusion_window6_fibonacci_resonance_threshold_lock_midBand ↔
          Nat.fib 6 ≤ n ∧ n < Nat.fib 7) ∧
        (n ∈ conclusion_window6_fibonacci_resonance_threshold_lock_highBand ↔
          Nat.fib 7 ≤ n ∧ n < Nat.fib 8))

/-- Paper label: `thm:conclusion-window6-fibonacci-resonance-threshold-lock`. The finite
window-6 arithmetic locks the resonance thresholds to `F_6 = 8`, `F_7 = 13`, and the ambient
modulus `F_8 = 21`. -/
theorem paper_conclusion_window6_fibonacci_resonance_threshold_lock :
    conclusion_window6_fibonacci_resonance_threshold_lock_statement := by
  have hf6 : Nat.fib 6 = 8 := by decide
  have hf7 : Nat.fib 7 = 13 := by decide
  have hf8 : Nat.fib 8 = 21 := by decide
  refine ⟨hf6, hf7, hf8, ?_⟩
  intro n hn
  simp [conclusion_window6_fibonacci_resonance_threshold_lock_lowBand,
    conclusion_window6_fibonacci_resonance_threshold_lock_midBand,
    conclusion_window6_fibonacci_resonance_threshold_lock_highBand, hf6, hf7, hf8] at *
  omega

end Omega.Conclusion
