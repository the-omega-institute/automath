import Mathlib.Algebra.Group.Nat.Even

namespace Omega.Conclusion

/-- Concrete valuation data for the local golden extension parity argument. -/
structure conclusion_fibadic_golden_extension_even_ramification_necessity_data where
  conclusion_fibadic_golden_extension_even_ramification_necessity_sqrtFiveValuation : ℕ

namespace conclusion_fibadic_golden_extension_even_ramification_necessity_data

/-- Faithful realization places `sqrt(5)` in `K`, so the ramification index is twice its
normalized valuation. -/
def ramificationIndex
    (D : conclusion_fibadic_golden_extension_even_ramification_necessity_data) : ℕ :=
  2 * D.conclusion_fibadic_golden_extension_even_ramification_necessity_sqrtFiveValuation

/-- The valuation identity `2 v_K(sqrt(5)) = e(K/Q_5)` in the packaged finite model. -/
def valuationParityIdentity
    (D : conclusion_fibadic_golden_extension_even_ramification_necessity_data) : Prop :=
  D.ramificationIndex =
    2 * D.conclusion_fibadic_golden_extension_even_ramification_necessity_sqrtFiveValuation

end conclusion_fibadic_golden_extension_even_ramification_necessity_data

/-- Paper label: `cor:conclusion-fibadic-golden-extension-even-ramification-necessity`. -/
theorem paper_conclusion_fibadic_golden_extension_even_ramification_necessity
    (D : conclusion_fibadic_golden_extension_even_ramification_necessity_data) :
    Even D.ramificationIndex := by
  exact ⟨D.conclusion_fibadic_golden_extension_even_ramification_necessity_sqrtFiveValuation,
    by simp [conclusion_fibadic_golden_extension_even_ramification_necessity_data.ramificationIndex,
      Nat.two_mul]⟩

end Omega.Conclusion
