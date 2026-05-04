import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-window6-boundary-ramanujan-conductor-three-rigid-uniqueness`. -/
theorem paper_conclusion_window6_boundary_ramanujan_conductor_three_rigid_uniqueness
    (a0 a1 a2 : ℚ) (h_const : a0 + a1 + a2 = 0) (h_u : a0 - a2 = 1)
    (h_v : a1 - a2 = 0) :
    a0 = (2 : ℚ) / 3 ∧ a1 = -(1 : ℚ) / 3 ∧ a2 = -(1 : ℚ) / 3 := by
  constructor
  · linarith
  · constructor <;> linarith

end Omega.Conclusion
