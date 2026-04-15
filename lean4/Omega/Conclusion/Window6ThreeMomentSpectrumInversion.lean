import Mathlib.Tactic
import Omega.Conclusion.Window6Collision

namespace Omega.Conclusion

/-- Invert the first three moment equations on the support `{2,3,4}`.
    thm:conclusion-window6-three-moment-spectrum-inversion -/
theorem paper_conclusion_window6_three_moment_spectrum_inversion
    (S0 S1 S2 N2 N3 N4 : ℤ)
    (h0 : S0 = N2 + N3 + N4)
    (h1 : S1 = 2 * N2 + 3 * N3 + 4 * N4)
    (h2 : S2 = 4 * N2 + 9 * N3 + 16 * N4) :
    N2 = (12 * S0 - 7 * S1 + S2) / 2 ∧
      N3 = -8 * S0 + 6 * S1 - S2 ∧
      N4 = (6 * S0 - 5 * S1 + S2) / 2 := by
  have hN2 : 12 * S0 - 7 * S1 + S2 = 2 * N2 := by
    nlinarith [h0, h1, h2]
  have hN3 : -8 * S0 + 6 * S1 - S2 = N3 := by
    nlinarith [h0, h1, h2]
  have hN4 : 6 * S0 - 5 * S1 + S2 = 2 * N4 := by
    nlinarith [h0, h1, h2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hN2]
    simpa using (Int.ediv_mul_cancel (show (2 : ℤ) ∣ 2 * N2 by exact dvd_mul_right _ _)).symm
  · exact hN3.symm
  · rw [hN4]
    simpa using (Int.ediv_mul_cancel (show (2 : ℤ) ∣ 2 * N4 by exact dvd_mul_right _ _)).symm

/-- Window-6 specialization recovers the histogram `(8,4,9)` from `(S0,S1,S2) = (21,64,212)`. -/
theorem window6_three_moment_spectrum_histogram :
    ((12 * (21 : ℤ) - 7 * 64 + 212) / 2 = 8) ∧
      (-8 * (21 : ℤ) + 6 * 64 - 212 = 4) ∧
      ((6 * (21 : ℤ) - 5 * 64 + 212) / 2 = 9) := by
  have htriple := window6_qmoment_triple
  rcases htriple with ⟨h0, h1, h2⟩
  have hinv :=
    paper_conclusion_window6_three_moment_spectrum_inversion
      21 64 212 8 4 9 (by simpa using h0) (by simpa using h1) (by simpa using h2)
  simpa using hinv

/-- The concrete window-6 Wedderburn second moment matches the same recovered histogram. -/
theorem window6_three_moment_spectrum_wedderburn :
    4 * (8 : ℤ) + 9 * 4 + 16 * 9 = 212 := by
  norm_num

end Omega.Conclusion
