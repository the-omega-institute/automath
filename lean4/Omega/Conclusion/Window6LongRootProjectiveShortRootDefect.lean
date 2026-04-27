import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-long-root-projective-short-root-defect`. -/
theorem paper_conclusion_window6_long_root_projective_short_root_defect
    (dLong dShort : Nat -> Nat)
    (hL0 : dLong 0 = 4) (hL1 : dLong 1 = 2) (hL2 : dLong 2 = 3)
    (hL3 : dLong 3 = 4) (hL4 : dLong 4 = 2) (hL5 : dLong 5 = 3)
    (hS0 : dShort 0 = 4) (hS1 : dShort 1 = 4) (hS2 : dShort 2 = 4)
    (hS3 : dShort 3 = 2) (hS4 : dShort 4 = 4) (hS5 : dShort 5 = 4) :
    (∀ j, j < 3 -> dLong j = dLong (j + 3)) ∧ dShort 0 ≠ dShort 3 ∧
      dShort 1 = dShort 4 ∧ dShort 2 = dShort 5 := by
  constructor
  · intro j hj
    interval_cases j
    · rw [hL0, hL3]
    · rw [hL1, hL4]
    · rw [hL2, hL5]
  · constructor
    · rw [hS0, hS3]
      decide
    · constructor
      · rw [hS1, hS4]
      · rw [hS2, hS5]

end Omega.Conclusion
