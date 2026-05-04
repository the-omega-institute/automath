import Omega.Conclusion.Window6Collision

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-histogram-generator-fivefold-decoding`. -/
theorem paper_conclusion_window6_histogram_generator_fivefold_decoding :
    8 + 4 + 9 = 21 ∧
      8 * 2 + 4 * 3 + 9 * 4 = 64 ∧
      (8 * 2 + 4 * 3 + 9 * 4) - (8 + 4 + 9) = 43 ∧
      8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2 = 212 ∧
      8 * 1 + 4 * 3 + 9 * 6 = 74 := by
  rcases window6_qmoment_triple with ⟨h0, h1, _⟩
  exact ⟨h0, h1, by norm_num, window6_S2_wedderburn, by norm_num⟩

end Omega.Conclusion
