import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-hardening-time-frontier-rigidity`. -/
theorem paper_xi_hardening_time_frontier_rigidity
    (m : Nat) (nMin logInvEps alpha Gamma : ℝ) (hGamma : 0 < Gamma)
    (hBudget : alpha * (m : ℝ) ≤ logInvEps) (hDelay : logInvEps / Gamma ≤ nMin) :
    alpha * (m : ℝ) / Gamma ≤ nMin := by
  rw [div_le_iff₀ hGamma]
  have hLog : logInvEps ≤ nMin * Gamma := by
    exact (div_le_iff₀ hGamma).1 hDelay
  linarith

end Omega.Zeta
