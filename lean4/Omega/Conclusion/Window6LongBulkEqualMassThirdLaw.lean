import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-long-bulk-equal-mass-third-law`. -/
theorem paper_conclusion_window6_long_bulk_equal_mass_third_law {Band Point : Type*}
    (I1 I2 I3 : Band) (mass : Band → ℚ) (N : Point → ℚ)
    (a1 b1 b2 a2 a3 b3 : Point)
    (hmass :
      mass I1 = (1 : ℚ) / 3 ∧ mass I2 = (1 : ℚ) / 3 ∧ mass I3 = (1 : ℚ) / 3)
    (hendpoint :
      N a1 = 0 ∧ N b1 = (1 : ℚ) / 3 ∧ N b2 = (1 : ℚ) / 3 ∧
        N a2 = (2 : ℚ) / 3 ∧ N a3 = (2 : ℚ) / 3 ∧ N b3 = 1) :
    mass I1 = (1 : ℚ) / 3 ∧ mass I2 = (1 : ℚ) / 3 ∧
      mass I3 = (1 : ℚ) / 3 ∧ N a1 = 0 ∧ N b1 = (1 : ℚ) / 3 ∧
        N b2 = (1 : ℚ) / 3 ∧ N a2 = (2 : ℚ) / 3 ∧
          N a3 = (2 : ℚ) / 3 ∧ N b3 = 1 := by
  exact
    ⟨hmass.1, hmass.2.1, hmass.2.2, hendpoint.1, hendpoint.2.1,
      hendpoint.2.2.1, hendpoint.2.2.2.1, hendpoint.2.2.2.2.1,
      hendpoint.2.2.2.2.2⟩

end Omega.Conclusion
