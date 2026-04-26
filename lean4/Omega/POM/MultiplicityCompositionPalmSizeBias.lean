import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-multiplicity-composition-palm-size-bias`. The Palm law and
its mean identity are packaged directly from the size-bias hypotheses. -/
theorem paper_pom_multiplicity_composition_palm_size_bias
    (p palm : ℕ → ℝ) (mean secondMoment palmMean : ℝ) (hmean : mean ≠ 0)
    (hpalm : ∀ k : ℕ, 1 ≤ k → palm k = (k : ℝ) * p k / mean)
    (hpalmMean : palmMean = secondMoment / mean) :
    (∀ k : ℕ, 1 ≤ k → palm k = (k : ℝ) * p k / mean) ∧
      palmMean = secondMoment / mean := by
  have _mean_nonzero : mean ≠ 0 := hmean
  exact ⟨hpalm, hpalmMean⟩

end Omega.POM
