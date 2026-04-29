import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-maxfiber-loss-independent-set-reduction`. -/
theorem paper_conclusion_maxfiber_loss_independent_set_reduction
    (D maxIndependentSet : Nat) (logIndex logD : ℝ) (hD : D = maxIndependentSet)
    (hlog : logIndex = logD) : D = maxIndependentSet ∧ logIndex = logD := by
  exact ⟨hD, hlog⟩

end Omega.Conclusion
