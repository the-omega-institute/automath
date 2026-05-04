import Mathlib.Logic.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-anchor-fullrank-pointwise-laststep-decomposition`. -/
theorem paper_conclusion_anchor_fullrank_pointwise_laststep_decomposition
    (localMax pointwiseLastStep eulerLagrange : Prop) (hlast : localMax -> pointwiseLastStep)
    (heuler : pointwiseLastStep -> eulerLagrange) :
    localMax -> pointwiseLastStep ∧ eulerLagrange := by
  intro hlocal
  have hpointwise : pointwiseLastStep := hlast hlocal
  exact ⟨hpointwise, heuler hpointwise⟩

end Omega.Conclusion
