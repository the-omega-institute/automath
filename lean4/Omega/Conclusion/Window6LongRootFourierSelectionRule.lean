import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-long-root-fourier-selection-rule`.
The window-six profile `(4, 2, 3, 4, 2, 3)` cancels in the odd Fourier modes when
`ζ ^ 3 = -1`. -/
theorem paper_conclusion_window6_long_root_fourier_selection_rule {R : Type*} [CommRing R]
    (ζ : R) (hζ : ζ ^ 3 = -1) :
    (4 + 2 * ζ + 3 * ζ ^ 2 + 4 * ζ ^ 3 + 2 * ζ ^ 4 + 3 * ζ ^ 5 = 0) ∧
      (4 + 2 * ζ ^ 3 + 3 * ζ ^ 6 + 4 * ζ ^ 9 + 2 * ζ ^ 12 + 3 * ζ ^ 15 = 0) ∧
        (4 + 2 * ζ ^ 5 + 3 * ζ ^ 10 + 4 * ζ ^ 15 + 2 * ζ ^ 20 + 3 * ζ ^ 25 = 0) := by
  have hζ9 : ζ ^ 9 = -1 := by
    calc
      ζ ^ 9 = (ζ ^ 3) ^ 3 := by ring
      _ = -1 := by rw [hζ]; ring
  have hζ15 : ζ ^ 15 = -1 := by
    calc
      ζ ^ 15 = (ζ ^ 3) ^ 5 := by ring
      _ = -1 := by rw [hζ]; ring
  constructor
  · calc
      4 + 2 * ζ + 3 * ζ ^ 2 + 4 * ζ ^ 3 + 2 * ζ ^ 4 + 3 * ζ ^ 5 =
          (ζ ^ 3 + 1) * (4 + 2 * ζ + 3 * ζ ^ 2) := by ring
      _ = 0 := by simp [hζ]
  constructor
  · calc
      4 + 2 * ζ ^ 3 + 3 * ζ ^ 6 + 4 * ζ ^ 9 + 2 * ζ ^ 12 + 3 * ζ ^ 15 =
          (1 + ζ ^ 9) * (4 + 2 * ζ ^ 3 + 3 * ζ ^ 6) := by ring
      _ = 0 := by simp [hζ9]
  · calc
      4 + 2 * ζ ^ 5 + 3 * ζ ^ 10 + 4 * ζ ^ 15 + 2 * ζ ^ 20 + 3 * ζ ^ 25 =
          (1 + ζ ^ 15) * (4 + 2 * ζ ^ 5 + 3 * ζ ^ 10) := by ring
      _ = 0 := by simp [hζ15]

end Omega.Conclusion
