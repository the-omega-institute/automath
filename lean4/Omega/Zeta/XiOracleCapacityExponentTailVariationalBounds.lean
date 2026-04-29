import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-oracle-capacity-exponent-tail-variational-bounds`. -/
theorem paper_xi_oracle_capacity_exponent_tail_variational_bounds
    (logPhi lowerTail upperTail lowerSigma upperSigma : ℝ)
    (hBase : logPhi ≤ lowerSigma)
    (hTail : lowerTail ≤ lowerSigma)
    (hSigma : lowerSigma ≤ upperSigma)
    (hUpper : upperSigma ≤ max logPhi upperTail) :
    max logPhi lowerTail ≤ lowerSigma ∧ lowerSigma ≤ upperSigma ∧
      upperSigma ≤ max logPhi upperTail := by
  exact ⟨max_le hBase hTail, hSigma, hUpper⟩

end Omega.Zeta
