import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-endpoint-radius-cauchy-window-triple-identity`. -/
theorem paper_conclusion_endpoint_radius_cauchy_window_triple_identity (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1) :
    let Gamma : ℝ := (1 + r) / (1 - r)
    let yminus : ℝ := (1 - r) / (1 + r)
    let yplus : ℝ := (1 + r) / (1 - r)
    yminus = 1 / Gamma ∧ yplus = Gamma ∧ yminus * yplus = 1 ∧
      1 - r ^ 2 = 4 * Gamma / (1 + Gamma) ^ 2 := by
  dsimp
  have hsub : (1 - r : ℝ) ≠ 0 := by linarith
  have hadd : (1 + r : ℝ) ≠ 0 := by linarith
  have hGamma_sum :
      (1 + (1 + r) / (1 - r) : ℝ) = 2 / (1 - r) := by
    field_simp [hsub]
    ring
  refine ⟨?_, rfl, ?_, ?_⟩
  · field_simp [hsub, hadd]
  · field_simp [hsub, hadd]
  · rw [hGamma_sum]
    field_simp [hsub]
    ring

end Omega.Conclusion
