import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9x-screen-completion-cost-sharp-area-law`.
The screen-completion cost is the relative-homology component deficit, and the axial-screen
component count gives the sharp area-law value. -/
theorem paper_xi_time_part9x_screen_completion_cost_sharp_area_law {Screen : Type*}
    (Cost components : Screen → ℕ) (axis : Screen) (m n : ℕ)
    (hCost : ∀ S, Cost S = components S - 1)
    (hAxis : components axis = 2 ^ (m * (n - 1)) + 1) :
    (∀ S, Cost S = components S - 1) ∧ Cost axis = 2 ^ (m * (n - 1)) := by
  refine ⟨hCost, ?_⟩
  calc
    Cost axis = components axis - 1 := hCost axis
    _ = (2 ^ (m * (n - 1)) + 1) - 1 := by rw [hAxis]
    _ = 2 ^ (m * (n - 1)) := by simp

end Omega.Zeta
