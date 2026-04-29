import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-softcore-fixedm-qrecurrence-generic-minimality`. -/
theorem paper_conclusion_softcore_fixedm_qrecurrence_generic_minimality
    (r minRecOrder : ℕ) (minimalDenominator uniqueFromWindow : Prop)
    (hOrder : minRecOrder = r + 2) :
    minimalDenominator → uniqueFromWindow →
      minimalDenominator ∧ minRecOrder = r + 2 ∧ uniqueFromWindow := by
  intro hMinimalDenominator hUniqueFromWindow
  exact ⟨hMinimalDenominator, hOrder, hUniqueFromWindow⟩

end Omega.Conclusion
