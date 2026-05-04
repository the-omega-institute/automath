import Omega.Conclusion.GoldenAlternatingConstantsRecoverPhi

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-golden-two-phase-cocycle-minimality`. -/
theorem paper_conclusion_window6_golden_two_phase_cocycle_minimality
    (a : ℝ) (ha : a ≠ 1 / 30) :
    ((1 / 2 + a) + (1 / 2 - a + 1 / 15)) / 2 = 8 / 15 ∧
      ((1 / 2 + a) - (1 / 2 - a + 1 / 15)) / 2 = a - 1 / 30 ∧
      (1 / 2 + a) ≠ (1 / 2 - a + 1 / 15) := by
  exact paper_conclusion_golden_fibonacci_two_phase_renormalization a ha

end Omega.Conclusion
