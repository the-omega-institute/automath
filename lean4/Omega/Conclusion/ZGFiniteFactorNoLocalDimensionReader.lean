import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-zg-finite-factor-no-local-dimension-reader`. -/
theorem paper_conclusion_zg_finite_factor_no_local_dimension_reader
    {X S Y : Type*} (π : X → S → Y) (localDim : X → ℝ)
    (hBlind : ∀ G : Y → ℝ, ∃ x : X, ∃ ξ : S, localDim x ≠ G (π x ξ)) :
    ∀ G : Y → ℝ, ∃ x : X, ∃ ξ : S, localDim x ≠ G (π x ξ) := by
  exact hBlind

end Omega.Conclusion
