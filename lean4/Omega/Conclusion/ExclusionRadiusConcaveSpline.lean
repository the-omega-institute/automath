import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `cor:conclusion-exclusion-radius-concave-spline`. -/
theorem paper_conclusion_exclusion_radius_concave_spline
    (s : ℕ) (x : ℝ) (m : Fin s → ℕ) (xj : Fin s → ℝ) (Delta R : ℝ → ℝ)
    (hDelta : Delta x = ∑ j, (m j : ℝ) * max (x - xj j) 0)
    (hR : R x = x - Delta x) :
    R x = x - ∑ j, (m j : ℝ) * max (x - xj j) 0 := by
  rw [hR, hDelta]

end Omega.Conclusion
