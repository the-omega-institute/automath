import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-star-moment-visible-complexity-quadratic`. -/
theorem paper_conclusion_star_moment_visible_complexity_quadratic
    (q degree realization compressed : ℕ) (hdeg : degree ≤ realization)
    (hreal : realization ≤ compressed) (hcomp : compressed ≤ ((q + 1) * q) / 2) :
    degree ≤ ((q + 1) * q) / 2 ∧ realization ≤ ((q + 1) * q) / 2 := by
  exact ⟨le_trans hdeg (le_trans hreal hcomp), le_trans hreal hcomp⟩

end Omega.Conclusion
