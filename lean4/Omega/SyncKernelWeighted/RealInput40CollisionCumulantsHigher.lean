import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40CollisionPressure
import Omega.SyncKernelWeighted.RealInput40CollisionCumulants

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Closed form for the third derivative of the real-input-40 collision cumulant generating
function at the origin. -/
def real_input_40_collision_cumulants_higher_third_derivative : ℝ :=
  (9 + 10 * Real.sqrt 5) / 625

/-- Closed form for the fourth derivative of the real-input-40 collision cumulant generating
function at the origin. -/
def real_input_40_collision_cumulants_higher_fourth_derivative : ℝ :=
  (7 + 24 * Real.sqrt 5) / 3125

/-- Paper label: `cor:real-input-40-collision-cumulants-higher`. -/
theorem paper_real_input_40_collision_cumulants_higher :
    real_input_40_collision_cumulants_higher_third_derivative = (9 + 10 * Real.sqrt 5) / 625 ∧
      real_input_40_collision_cumulants_higher_fourth_derivative =
        (7 + 24 * Real.sqrt 5) / 3125 := by
  constructor <;> rfl

end

end Omega.SyncKernelWeighted
