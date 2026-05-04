import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-rational-functional-calculus-no-18plus3-image`. -/
theorem paper_conclusion_window6_rational_functional_calculus_no_18plus3_image
    (rank : ℕ) (hrank : rank = 0 ∨ rank = 1 ∨ rank = 20 ∨ rank = 21) :
    rank ≠ 18 ∧ rank ≠ 3 := by
  constructor
  · intro h18
    rcases hrank with h0 | h1 | h20 | h21 <;> omega
  · intro h3
    rcases hrank with h0 | h1 | h20 | h21 <;> omega

end Omega.Conclusion
