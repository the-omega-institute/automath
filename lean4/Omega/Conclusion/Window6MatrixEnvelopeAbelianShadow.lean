import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-matrix-envelope-abelian-shadow`. The
window-`6` Wedderburn shadow splits the matrix-envelope dimension into its center and
commutator dimensions. -/
theorem paper_conclusion_window6_matrix_envelope_abelian_shadow :
    8 + 4 + 9 = 21 ∧
      8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2 = 212 ∧
      8 * (2 ^ 2 - 1) + 4 * (3 ^ 2 - 1) + 9 * (4 ^ 2 - 1) = 191 ∧
      212 = 191 + 21 := by
  omega

end Omega.Conclusion
