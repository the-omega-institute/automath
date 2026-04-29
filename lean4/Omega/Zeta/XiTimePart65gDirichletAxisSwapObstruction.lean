import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65g-dirichlet-axis-swap-obstruction`. -/
theorem paper_xi_time_part65g_dirichlet_axis_swap_obstruction
    (D : ℝ → ℂ) (t0 : ℝ)
    (hDirichletAxisSwap :
      (∀ t : ℝ, (D (t + t0)).re = (D t).im ∧ (D (t + t0)).im = (D t).re) →
        ∀ t : ℝ, D t = 0)
    (hSwap :
      ∀ t : ℝ, (D (t + t0)).re = (D t).im ∧ (D (t + t0)).im = (D t).re) :
    ∀ t : ℝ, D t = 0 := by
  exact hDirichletAxisSwap hSwap

end Omega.Zeta
