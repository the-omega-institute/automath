import Mathlib.Tactic
import Omega.GU.TerminalFoldbin6BitflipStabilityAk

namespace Omega.Conclusion

/-- Paper-facing window-6 noise-stability statement in terms of the verified shell coefficients. -/
def conclusion_window6_noise_local_fragility_high_order_return_statement : Prop :=
  Omega.GU.terminalFoldbin6StabilityCoeff 1 = 0 ∧
    (∀ k : ℕ, 2 ≤ k → k ≤ 6 → 0 < Omega.GU.terminalFoldbin6StabilityCoeff k) ∧
      Omega.GU.terminalFoldbin6StabilityCoeff 5 =
        Omega.GU.terminalFoldbin6StabilityCoeff 6 ∧
        Omega.GU.terminalFoldbin6StabilityCoeff 3 <
          Omega.GU.terminalFoldbin6StabilityCoeff 5

/-- Paper label: `thm:conclusion-window6-noise-local-fragility-high-order-return`. -/
theorem paper_conclusion_window6_noise_local_fragility_high_order_return :
    conclusion_window6_noise_local_fragility_high_order_return_statement := by
  rcases Omega.GU.paper_terminal_foldbin6_bitflip_stability_Ak with
    ⟨_, h1, h2, h3, h4, h5, h6⟩
  refine ⟨h1, ?_, ?_, ?_⟩
  · intro k hk2 hk6
    interval_cases k <;> simp [h2, h3, h4, h5, h6]
  · rw [h5, h6]
  · rw [h3, h5]
    norm_num

end Omega.Conclusion
