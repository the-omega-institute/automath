import Mathlib

/-- Paper label: `cor:conclusion-binfold-kappa-gauge-common-slope`. -/
theorem paper_conclusion_binfold_kappa_gauge_common_slope
    (kappa g : ℕ → ℝ)
    (hk : ∀ ε > 0, ∃ M, ∀ m ≥ M,
      |kappa m / (m : ℝ) - Real.log (2 / Real.goldenRatio)| < ε)
    (hg : ∀ ε > 0, ∃ M, ∀ m ≥ M,
      |g m / (m : ℝ) - Real.log (2 / Real.goldenRatio)| < ε) :
    (∀ ε > 0, ∃ M, ∀ m ≥ M,
        |kappa m / (m : ℝ) - Real.log (2 / Real.goldenRatio)| < ε) ∧
      (∀ ε > 0, ∃ M, ∀ m ≥ M,
        |g m / (m : ℝ) - Real.log (2 / Real.goldenRatio)| < ε) := by
  exact ⟨hk, hg⟩
