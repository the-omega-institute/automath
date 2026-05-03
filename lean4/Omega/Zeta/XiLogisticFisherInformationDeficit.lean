import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-logistic-fisher-information-deficit`.
The Fisher information is bounded by the one-component logistic Fisher constant once the
deficit has been identified as a nonnegative conditional-variance term. -/
theorem paper_xi_logistic_fisher_information_deficit (I deficit : ℝ)
    (hI : I = (1 / 3 : ℝ) - deficit) (hdef : 0 ≤ deficit) :
    I ≤ (1 / 3 : ℝ) := by
  rw [hI]
  linarith

end Omega.Zeta
