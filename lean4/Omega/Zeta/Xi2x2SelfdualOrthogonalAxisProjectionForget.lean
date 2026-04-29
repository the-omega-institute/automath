import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- Paper label: `cor:xi-2x2-selfdual-orthogonal-axis-projection-forget`. -/
theorem paper_xi_2x2_selfdual_orthogonal_axis_projection_forget
    (rho theta rho' : ℝ) (hneq : rho ≠ rho') :
    (fun p : ℝ × ℝ => p.2) (rho, theta) = (fun p : ℝ × ℝ => p.2) (rho', theta) ∧
      ((rho, theta).1 = 0 ↔ rho = 0) := by
  have _ : rho ≠ rho' := hneq
  exact ⟨rfl, Iff.rfl⟩

end Omega.Zeta
