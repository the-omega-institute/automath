import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-max-algorithmic-uplift-maxfiber-log`. -/
theorem paper_conclusion_max_algorithmic_uplift_maxfiber_log
    {X Ω : Type*} [Fintype X] [Fintype Ω] [DecidableEq X]
    (Fold : Ω → X) (KΩ : Ω → ℝ) (KX : X → ℝ) (M err : ℝ)
    (fiberSize : X → ℕ) (_hM : ∀ x, (fiberSize x : ℝ) ≤ M)
    (hUpper : ∀ ω, KΩ ω - KX (Fold ω) ≤ Real.log M / Real.log 2 + err)
    (hLower :
      ∃ x : X, (fiberSize x : ℝ) = M ∧
        ∃ ω : Ω, Fold ω = x ∧
          Real.log M / Real.log 2 - err ≤ KΩ ω - KX x) :
    (∀ ω, KΩ ω - KX (Fold ω) ≤ Real.log M / Real.log 2 + err) ∧
      ∃ ω, Real.log M / Real.log 2 - err ≤ KΩ ω - KX (Fold ω) := by
  refine ⟨hUpper, ?_⟩
  rcases hLower with ⟨x, _hxM, ω, hFold, hω⟩
  refine ⟨ω, ?_⟩
  simpa [hFold] using hω

end Omega.Conclusion
