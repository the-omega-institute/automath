import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-detectability-amplitude-is-quadratic-image`. -/
theorem paper_xi_detectability_amplitude_is_quadratic_image (δ : ℝ) (hδ : 0 < δ) :
    let p : ℝ := δ / (1 + δ)
    let a : ℝ := 4 * δ / (1 + δ) ^ 2
    a = 4 * p * (1 - p) := by
  have hden : (1 + δ : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  ring

end Omega.Zeta
