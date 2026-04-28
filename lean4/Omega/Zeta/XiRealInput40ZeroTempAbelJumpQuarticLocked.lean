import Omega.Zeta.XiRealInput40ZeroTempCoreAbelConstantSplitting

namespace Omega.Zeta

noncomputable section

/-- Paper label: `thm:xi-real-input40-zero-temp-abel-jump-quartic-locked`. -/
theorem paper_xi_real_input40_zero_temp_abel_jump_quartic_locked
    (D : xi_real_input40_zero_temp_core_abel_constant_splitting_data) (b : ℝ)
    (hQuartic : 1 - 6 * b + 9 * b ^ 2 - b ^ 3 - b ^ 4 = 0)
    (hMaxPositiveRoot :
      ∀ c : ℝ, 0 < c → 1 - 6 * c + 9 * c ^ 2 - c ^ 3 - c ^ 4 = 0 → c ≤ b)
    (hJump : D.logMInf - D.logMCoreInf = b) :
    (1 - 6 * b + 9 * b ^ 2 - b ^ 3 - b ^ 4 = 0) ∧
      (∀ c : ℝ, 0 < c → 1 - 6 * c + 9 * c ^ 2 - c ^ 3 - c ^ 4 = 0 → c ≤ b) ∧
      D.logMInf = D.logMCoreInf + b := by
  refine ⟨hQuartic, hMaxPositiveRoot, ?_⟩
  linarith

end

end Omega.Zeta
