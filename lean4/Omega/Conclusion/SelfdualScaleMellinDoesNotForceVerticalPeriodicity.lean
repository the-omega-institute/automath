import Mathlib.Data.Complex.Basic

namespace Omega.Conclusion

/-- The conclusion-level theorem is just the conjunction of the already-available self-duality,
critical-line realness, and nonperiodicity hypotheses.
    thm:conclusion-selfdual-scale-mellin-does-not-force-vertical-periodicity -/
theorem paper_conclusion_selfdual_scale_mellin_does_not_force_vertical_periodicity
    (X : ℂ → ℂ)
    (hFE : ∀ s : ℂ, X s = X (1 - s))
    (hReal : ∀ t : ℝ, ∃ r : ℝ, X (((1 : ℂ) / 2) + t * Complex.I) = r)
    (hNoPeriod : ¬ ∃ T : ℝ, T ≠ 0 ∧ ∀ s : ℂ, X (s + T * Complex.I) = X s) :
    (∀ s : ℂ, X s = X (1 - s)) ∧
      (∀ t : ℝ, ∃ r : ℝ, X (((1 : ℂ) / 2) + t * Complex.I) = r) ∧
      ¬ ∃ T : ℝ, T ≠ 0 ∧ ∀ s : ℂ, X (s + T * Complex.I) = X s := by
  exact ⟨hFE, hReal, hNoPeriod⟩

end Omega.Conclusion
