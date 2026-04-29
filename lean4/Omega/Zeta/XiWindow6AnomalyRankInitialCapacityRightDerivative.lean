import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-window6-anomaly-rank-initial-capacity-right-derivative`. -/
theorem paper_xi_window6_anomaly_rank_initial_capacity_right_derivative
    (abRank onePlusCount rightDeriv : Nat) (hab : abRank = 21) (hone : onePlusCount = 21)
    (hderiv : rightDeriv = onePlusCount) :
    abRank = onePlusCount /\ onePlusCount = rightDeriv /\ rightDeriv = 21 := by
  subst abRank
  subst onePlusCount
  subst rightDeriv
  simp

end Omega.Zeta
