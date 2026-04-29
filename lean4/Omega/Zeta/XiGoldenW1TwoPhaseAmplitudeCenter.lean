import Mathlib.Tactic
import Omega.Zeta.XiGoldenW1TrueTwoPhaseLimit

namespace Omega.Zeta

/-- Paper label: `cor:xi-golden-w1-two-phase-amplitude-center`.
The explicit even/odd Fibonacci transport constants yield the stated two-phase amplitude and
arithmetic center formulas. -/
theorem paper_xi_golden_w1_two_phase_amplitude_center :
    Omega.Kronecker.goldenEvenScaledLimitConstant = (1 / 2 : ℝ) + 1 / (2 * Real.sqrt 5) ∧
      Omega.Kronecker.goldenOddScaledLimitConstant =
        (1 / 2 : ℝ) - 1 / (2 * Real.sqrt 5) + 1 / 15 ∧
      Omega.Kronecker.goldenEvenScaledLimitConstant ≠
        Omega.Kronecker.goldenOddScaledLimitConstant ∧
      Omega.Kronecker.goldenEvenScaledLimitConstant -
          Omega.Kronecker.goldenOddScaledLimitConstant =
        1 / Real.sqrt 5 - 1 / 15 ∧
      (Omega.Kronecker.goldenEvenScaledLimitConstant +
          Omega.Kronecker.goldenOddScaledLimitConstant) / 2 =
        8 / 15 := by
  rcases paper_xi_golden_w1_true_two_phase_limit with ⟨_, heven, hodd, hneq, _, _⟩
  have hsqrt5_pos : 0 < (Real.sqrt 5 : ℝ) := by positivity
  have hsqrt5_ne_zero : (Real.sqrt 5 : ℝ) ≠ 0 := ne_of_gt hsqrt5_pos
  refine ⟨heven, hodd, hneq, ?_, ?_⟩
  · rw [heven, hodd]
    field_simp [hsqrt5_ne_zero]
    ring
  · rw [heven, hodd]
    field_simp [hsqrt5_ne_zero]
    ring

end Omega.Zeta
