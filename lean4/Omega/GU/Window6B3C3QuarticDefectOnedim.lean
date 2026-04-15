import Mathlib.Tactic

namespace Omega.GU

/-- Paper-facing wrapper for the one-dimensional quartic defect in the `window-6` `B₃/C₃`
    sector, obtained by eliminating the mixed quartic term in favor of the second moment and the
    octahedral harmonic defect.  thm:window6-b3c3-quartic-defect-onedim -/
theorem paper_window6_b3c3_quartic_defect_onedim
    (s2 s4 h4 m2B m2C m4B m4C cross : ℝ)
    (hCross : s2 ^ 2 = s4 + 2 * cross)
    (hH4 : h4 = s4 - (3 / 5 : ℝ) * s2 ^ 2)
    (hM2B : m2B = 10 * s2)
    (hM2C : m2C = 16 * s2)
    (hM4B : m4B = 10 * s4 + 24 * cross)
    (hM4C : m4C = 40 * s4 + 24 * cross) :
    m2B = 10 * s2 ∧ m2C = 16 * s2 ∧
      m4B = (54 / 5 : ℝ) * s2 ^ 2 - 2 * h4 ∧
      m4C = (144 / 5 : ℝ) * s2 ^ 2 + 28 * h4 := by
  refine ⟨hM2B, hM2C, ?_, ?_⟩
  · nlinarith [hCross, hH4, hM4B]
  · nlinarith [hCross, hH4, hM4C]

end Omega.GU
