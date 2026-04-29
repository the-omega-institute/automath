import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-rational-envelope-reconstructs-block-spectrum`. -/
theorem paper_conclusion_window6_rational_envelope_reconstructs_block_spectrum :
    (21 - 13 = 8) ∧
      (13 - 9 = 4) ∧
      (8 + 4 + 9 = 21) ∧
      (8 * 2 + 4 * 3 + 9 * 4 = 64) ∧
      (8 + 4 + 9 * 3 = 39) ∧
      (4 + 9 = 13) := by
  norm_num

end Omega.Conclusion
