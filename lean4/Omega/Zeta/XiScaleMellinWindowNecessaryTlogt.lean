import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-scale-mellin-window-necessary-tlogt`. -/
theorem paper_xi_scale_mellin_window_necessary_tlogt
    (B : ℝ) (X scale logScale zeros : Nat → ℝ)
    (cartwright_bound : ∀ T, zeros T ≤ (2 * B) * X T * scale T)
    (small_window :
      ∀ c > 0, ∃ T0, ∀ T ≥ T0, (2 * B) * X T * scale T ≤ c * scale T * logScale T) :
    ∀ c > 0, ∃ T0, ∀ T ≥ T0, zeros T ≤ c * scale T * logScale T := by
  intro c hc
  obtain ⟨T0, hT0⟩ := small_window c hc
  refine ⟨T0, ?_⟩
  intro T hT
  exact le_trans (cartwright_bound T) (hT0 T hT)

end Omega.Zeta
