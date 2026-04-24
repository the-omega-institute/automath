import Omega.Kronecker.GoldenConvergentErrorClosed
import Omega.Kronecker.W1FibonacciLimits
import Omega.Kronecker.W1LipschitzPushforward

namespace Omega.Zeta

/-- Paper label: `thm:xi-golden-w1-true-two-phase-limit`.
The golden Kronecker branch inherits the universal Lipschitz `W₁` audit bound, has two distinct
Fibonacci subsequential constants on the even/odd phases, and therefore cannot admit a single
`C / F_n` asymptotic constant compatible with the exact signed convergent error formula. -/
theorem paper_xi_golden_w1_true_two_phase_limit :
    (∀ D : Omega.Kronecker.W1LipschitzPushforwardData, D.pushforwardBound) ∧
      Omega.Kronecker.goldenEvenScaledLimitConstant = (1 / 2 : ℝ) + 1 / (2 * Real.sqrt 5) ∧
      Omega.Kronecker.goldenOddScaledLimitConstant =
        (1 / 2 : ℝ) - 1 / (2 * Real.sqrt 5) + 1 / 15 ∧
      Omega.Kronecker.goldenEvenScaledLimitConstant ≠
        Omega.Kronecker.goldenOddScaledLimitConstant ∧
      (¬ ∃ C : ℝ,
        C = Omega.Kronecker.goldenEvenScaledLimitConstant ∧
          C = Omega.Kronecker.goldenOddScaledLimitConstant) ∧
      (∀ n : ℕ, 2 ≤ n →
        let α : ℝ := Real.goldenRatio⁻¹
        let q : ℝ := Nat.fib n
        α - (Nat.fib (n - 1) : ℝ) / q = (-1 : ℝ) ^ (n - 1) * α ^ n / q) := by
  have hpush :
      ∀ D : Omega.Kronecker.W1LipschitzPushforwardData, D.pushforwardBound := by
    intro D
    exact Omega.Kronecker.paper_kronecker_w1_lipschitz_pushforward D
  rcases Omega.Kronecker.paper_kronecker_w1_fibonacci_limits with ⟨heven, hodd⟩
  have hneq :
      Omega.Kronecker.goldenEvenScaledLimitConstant ≠
        Omega.Kronecker.goldenOddScaledLimitConstant := by
    intro hEq
    have hsqrt5_ne : (Real.sqrt 5 : ℝ) ≠ 15 := by
      intro h
      nlinarith [h, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
    rw [heven, hodd] at hEq
    have hsqrt5_pos : 0 < (Real.sqrt 5 : ℝ) := by positivity
    have hsqrt5_ne_zero : (Real.sqrt 5 : ℝ) ≠ 0 := ne_of_gt hsqrt5_pos
    field_simp [hsqrt5_ne_zero] at hEq
    have hsqrt5_eq : (Real.sqrt 5 : ℝ) = 15 := by
      linarith
    exact hsqrt5_ne hsqrt5_eq
  have hnosingle :
      ¬ ∃ C : ℝ,
        C = Omega.Kronecker.goldenEvenScaledLimitConstant ∧
          C = Omega.Kronecker.goldenOddScaledLimitConstant := by
    intro hC
    rcases hC with ⟨C, hCeven, hCodd⟩
    exact hneq (hCeven.symm.trans hCodd)
  refine ⟨hpush, heven, hodd, hneq, hnosingle, ?_⟩
  intro n hn
  simpa using Omega.Kronecker.paper_kronecker_golden_convergent_error_closed n hn

end Omega.Zeta
