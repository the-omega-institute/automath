import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-chain-tree-single-scalar-budget-controls-local-partial-correlations`. -/
theorem paper_conclusion_chain_tree_single_scalar_budget_controls_local_partial_correlations
    (R : Type*) (chainProjection allLocalBounds maxBound sqrtBound smallEntropyScale : Prop)
    (hLocalToMax : allLocalBounds → maxBound)
    (hSqrt : maxBound → sqrtBound)
    (hAsymptotic : sqrtBound → smallEntropyScale) :
    chainProjection → allLocalBounds → maxBound ∧ sqrtBound ∧ smallEntropyScale := by
  intro _ hAllLocal
  have hMax : maxBound := hLocalToMax hAllLocal
  have hSqrtBound : sqrtBound := hSqrt hMax
  exact ⟨hMax, hSqrtBound, hAsymptotic hSqrtBound⟩

end Omega.Conclusion
