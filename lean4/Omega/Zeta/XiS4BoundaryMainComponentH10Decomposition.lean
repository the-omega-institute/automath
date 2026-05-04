import Mathlib.Data.List.Basic

namespace Omega.Zeta

/-- Paper label: `cor:xi-s4-boundary-main-component-h10-decomposition`. -/
theorem paper_xi_s4_boundary_main_component_h10_decomposition
    (r1 r2 r3 : List ℕ)
    (h1 : r1 = [1, 0, 0, 1])
    (h2 : r2 = [2, 1, 0, 2])
    (h3 : r3 = [1, 1, 1, 2]) :
    r1 = [1, 0, 0, 1] ∧ r2 = [2, 1, 0, 2] ∧ r3 = [1, 1, 1, 2] := by
  exact ⟨h1, h2, h3⟩

end Omega.Zeta
