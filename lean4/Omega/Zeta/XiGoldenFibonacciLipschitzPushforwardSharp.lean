import Omega.Zeta.XiGoldenW1TrueTwoPhaseLimit

namespace Omega.Zeta

/-- Paper label: `thm:xi-golden-fibonacci-lipschitz-pushforward-sharp`. -/
theorem paper_xi_golden_fibonacci_lipschitz_pushforward_sharp :
    (∀ D : Omega.Kronecker.W1LipschitzPushforwardData, D.pushforwardBound) ∧
      Omega.Kronecker.goldenEvenScaledLimitConstant = (1 / 2 : ℝ) + 1 / (2 * Real.sqrt 5) ∧
      Omega.Kronecker.goldenOddScaledLimitConstant =
        (1 / 2 : ℝ) - 1 / (2 * Real.sqrt 5) + 1 / 15 := by
  rcases paper_xi_golden_w1_true_two_phase_limit with ⟨hpush, heven, hodd, _⟩
  exact ⟨hpush, heven, hodd⟩

end Omega.Zeta
