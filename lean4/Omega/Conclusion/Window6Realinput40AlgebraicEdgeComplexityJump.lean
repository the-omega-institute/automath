import Mathlib.Tactic

namespace Omega.Conclusion

/-- The audited algebraic edge complexity on the window-`6` side is quadratic. -/
def conclusion_window6_realinput40_algebraic_edge_complexity_jump_window6_degree : ℕ := 2

/-- The audited algebraic edge complexity on the real-input-`40` side is quartic. -/
def conclusion_window6_realinput40_algebraic_edge_complexity_jump_realinput40_degree : ℕ := 4

/-- Paper label: `prop:conclusion-window6-realinput40-algebraic-edge-complexity-jump`. The
window-`6` edge is packaged as quadratic while the real-input-`40` edge is packaged as quartic, so
the audited algebraic complexity jumps strictly from `2` to `4`. -/
theorem paper_conclusion_window6_realinput40_algebraic_edge_complexity_jump :
    conclusion_window6_realinput40_algebraic_edge_complexity_jump_window6_degree = 2 ∧
      conclusion_window6_realinput40_algebraic_edge_complexity_jump_realinput40_degree = 4 ∧
      conclusion_window6_realinput40_algebraic_edge_complexity_jump_window6_degree <
        conclusion_window6_realinput40_algebraic_edge_complexity_jump_realinput40_degree := by
  simp [conclusion_window6_realinput40_algebraic_edge_complexity_jump_window6_degree,
    conclusion_window6_realinput40_algebraic_edge_complexity_jump_realinput40_degree]

end Omega.Conclusion
