import Mathlib.Data.Rat.Defs

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-riccati-quadratic-field-ramification-ledger`.
The Riccati quadratic-field ramification ledger is transported along the supplied equivalence
between the ramification predicate and the discriminant-support predicate. -/
theorem paper_conclusion_riccati_quadratic_field_ramification_ledger
    (t : ℚ) (ht : 0 < t) (ramifiedPrime dividesDiscriminant : ℕ → Prop)
    (hquad : ∀ p, ramifiedPrime p ↔ dividesDiscriminant p) :
    ∀ p, ramifiedPrime p ↔ dividesDiscriminant p := by
  have _ := ht
  exact hquad

end Omega.Conclusion
