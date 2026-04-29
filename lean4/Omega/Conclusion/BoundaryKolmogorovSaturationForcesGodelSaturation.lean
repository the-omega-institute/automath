import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-boundary-kolmogorov-saturation-forces-godel-saturation`. -/
theorem paper_conclusion_boundary_kolmogorov_saturation_forces_godel_saturation {n : ℕ}
    {dBoundary : ℝ} (hLower : (n : ℝ) ≤ dBoundary) (hUpper : dBoundary ≤ (n : ℝ)) :
    dBoundary = (n : ℝ) := by
  exact le_antisymm hUpper hLower

end Omega.Conclusion
