import Mathlib.Data.Rat.Lemmas

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-hamming-tail-twolevel-platform`. -/
theorem paper_conclusion_window6_hamming_tail_twolevel_platform (A : Fin 7 → ℚ)
    (h0 : A 0 = 1) (h1 : A 1 = 0) (h2 : A 2 = (1 : ℚ) / 30)
    (h3 : A 3 = (1 : ℚ) / 40) (h4 : A 4 = (7 : ℚ) / 120)
    (h5 : A 5 = (1 : ℚ) / 16) (h6 : A 6 = (1 : ℚ) / 16) : A 5 = A 6 := by
  have _h0 : A 0 = 1 := h0
  have _h1 : A 1 = 0 := h1
  have _h2 : A 2 = (1 : ℚ) / 30 := h2
  have _h3 : A 3 = (1 : ℚ) / 40 := h3
  have _h4 : A 4 = (7 : ℚ) / 120 := h4
  rw [h5, h6]

end Omega.Conclusion
