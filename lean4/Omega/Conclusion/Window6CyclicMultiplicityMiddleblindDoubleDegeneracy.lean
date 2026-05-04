import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`cor:conclusion-window6-cyclic-multiplicity-middleblind-double-degeneracy`. -/
theorem paper_conclusion_window6_cyclic_multiplicity_middleblind_double_degeneracy
    (f2 f3 f4 : ℝ) (h42 : f4 = f2) (h32 : f3 ≠ f2) :
    let c : ℝ := (4 / 3) * (f3 - f2);
    c ≠ 0 ∧
      (c, -2 * c, c) =
        ((4 / 3) * (f3 - f2), (-8 / 3) * (f3 - f2), (4 / 3) * (f3 - f2)) := by
  have _ := h42
  dsimp
  constructor
  · exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr h32)
  · ring_nf

end Omega.Conclusion
