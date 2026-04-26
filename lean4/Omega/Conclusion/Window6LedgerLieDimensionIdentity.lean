import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-ledger-lie-dimension-identity`. -/
theorem paper_conclusion_window6_ledger_lie_dimension_identity (x6Card ledgerDim vDim : ℕ)
    (so21 sl21 : Prop) (hcard : x6Card = 21) (hledger : ledgerDim = x6Card)
    (hv : vDim = x6Card) (hso : so21) (hsl : sl21) :
    x6Card = ledgerDim ∧ ledgerDim = vDim ∧ vDim = 21 ∧ so21 ∧ sl21 := by
  subst x6Card
  subst ledgerDim
  subst vDim
  exact ⟨rfl, rfl, rfl, hso, hsl⟩

end Omega.Conclusion
