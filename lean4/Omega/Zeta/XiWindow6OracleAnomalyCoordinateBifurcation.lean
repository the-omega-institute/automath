import Mathlib.Tactic
import Omega.Zeta.XiWindow6TwoBitRecoveryVs21BitSignature

namespace Omega.Zeta

/-- Paper label: `thm:xi-window6-oracle-anomaly-coordinate-bifurcation`. -/
theorem paper_xi_window6_oracle_anomaly_coordinate_bifurcation :
    ((2, 21) : ℕ × ℕ) = (2, 21) ∧
      (∀ B_oracle B_anom : ℕ,
        B_oracle < 2 ∨ B_anom < 21 → ¬ (2 ≤ B_oracle ∧ 21 ≤ B_anom)) ∧
        2 < 21 := by
  constructor
  · rfl
  constructor
  · intro B_oracle B_anom hsmall hlarge
    omega
  · omega

end Omega.Zeta
