import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-discrete-phase-band-width-curvature-sampling`. -/
theorem paper_conclusion_discrete_phase_band_width_curvature_sampling
    (Lambda : ℤ → ℝ) (q : ℤ) (left right : ℝ)
    (hleft : left = Lambda (q - 1) - Lambda (q - 2))
    (hright : right = Lambda q - Lambda (q - 1)) :
    right - left = Lambda q - 2 * Lambda (q - 1) + Lambda (q - 2) := by
  rw [hleft, hright]
  ring

end Omega.Conclusion
