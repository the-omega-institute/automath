import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-oracle-capacity-exponent-closed-form-tail-spectrum`. -/
theorem paper_xi_oracle_capacity_exponent_closed_form_tail_spectrum
    (logPhi leftTail rightTail lowerSigma upperSigma : ℝ)
    (hBounds : max logPhi leftTail ≤ lowerSigma ∧ lowerSigma ≤ upperSigma ∧
      upperSigma ≤ max logPhi rightTail)
    (hTailClosed : leftTail = rightTail) :
    lowerSigma = max logPhi rightTail ∧ upperSigma = max logPhi rightTail := by
  rcases hBounds with ⟨hLower, hSigma, hUpper⟩
  have hTailLower : max logPhi rightTail ≤ lowerSigma := by
    simpa [hTailClosed] using hLower
  have hLowerEq : lowerSigma = max logPhi rightTail :=
    le_antisymm (le_trans hSigma hUpper) hTailLower
  have hUpperEq : upperSigma = max logPhi rightTail :=
    le_antisymm hUpper (hLowerEq ▸ hSigma)
  exact ⟨hLowerEq, hUpperEq⟩

end Omega.Zeta
