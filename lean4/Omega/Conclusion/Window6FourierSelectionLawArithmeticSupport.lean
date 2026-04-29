import Omega.Conclusion.Window6LongRootFourierSelectionRule

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-fourier-selection-law-arithmetic-support`. -/
theorem paper_conclusion_window6_fourier_selection_law_arithmetic_support {R : Type*}
    [CommRing R] (ζ : R) (hζ : ζ ^ 3 = -1) :
    (4 + 2 * ζ + 3 * ζ ^ 2 + 4 * ζ ^ 3 + 2 * ζ ^ 4 + 3 * ζ ^ 5 = 0) ∧
      (4 + 2 * ζ ^ 3 + 3 * ζ ^ 6 + 4 * ζ ^ 9 + 2 * ζ ^ 12 + 3 * ζ ^ 15 = 0) ∧
        (4 + 2 * ζ ^ 5 + 3 * ζ ^ 10 + 4 * ζ ^ 15 + 2 * ζ ^ 20 + 3 * ζ ^ 25 = 0) := by
  exact paper_conclusion_window6_long_root_fourier_selection_rule ζ hζ

end Omega.Conclusion
