import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-localized-directsum-twoaxis-ledger-cancellation`. Equal direct-sum
ledger totals with a common summand cancel on cardinalities and on each prime multiplicity. -/
theorem paper_xi_localized_directsum_twoaxis_ledger_cancellation
    (cardS cardT cardU : ℕ) (mS mT mU : ℕ → ℕ)
    (hcard : cardS + cardU = cardT + cardU)
    (hm : ∀ p : ℕ, mS p + mU p = mT p + mU p) :
    cardS = cardT ∧ ∀ p : ℕ, mS p = mT p := by
  constructor
  · omega
  · intro p
    have hp := hm p
    omega

end Omega.Zeta
