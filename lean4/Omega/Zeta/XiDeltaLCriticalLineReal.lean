import Mathlib.Data.Complex.Basic

namespace Omega.Zeta

/-- Paper label: `prop:xi-delta-L-critical-line-real`. If the critical-line section of `Xi`
is identified with a real-valued prefixed section `E`, then `Xi` itself has real values on
the critical line. -/
theorem paper_xi_delta_l_critical_line_real (Xi : ℂ → ℂ) (E : ℝ → ℂ)
    (hsection : ∀ t : ℝ, Xi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = E t)
    (hreal : ∀ t : ℝ, ∃ r : ℝ, E t = (r : ℂ)) :
    ∀ t : ℝ, ∃ r : ℝ, Xi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = (r : ℂ) := by
  intro t
  rcases hreal t with ⟨r, hr⟩
  exact ⟨r, by rw [hsection t, hr]⟩

end Omega.Zeta
