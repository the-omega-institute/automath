import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-leyang-symmetric-quotient-genus2`.
The symmetric quotient calculation records the hyperelliptic model and derives the genus-two
conclusion from that model. -/
theorem paper_conclusion_leyang_symmetric_quotient_genus2
    (birationalHyperellipticModel genusTwo : Prop)
    (hModel : birationalHyperellipticModel)
    (hGenus : birationalHyperellipticModel -> genusTwo) :
    birationalHyperellipticModel ∧ genusTwo := by
  exact ⟨hModel, hGenus hModel⟩

end Omega.Conclusion
