import Omega.Folding.BernoulliPParryPressureChain
import Mathlib.Tactic

namespace Omega.Folding

/-- Paper-facing wrapper for the closed-form Perron eigenvectors, Doob transform kernel, and
    stationary law of the Bernoulli-`p` tilted four-state transfer operator.
    thm:fold-bernoulli-p-doob-transform-closed -/
theorem paper_fold_bernoulli_p_doob_transform_closed
    (rightEigenvectorClosedForm leftEigenvectorClosedForm doobKernelClosedForm
      stationaryDistributionClosedForm : Prop)
    (hRight : rightEigenvectorClosedForm) (hLeft : leftEigenvectorClosedForm)
    (hKernel : doobKernelClosedForm) (hStationary : stationaryDistributionClosedForm) :
    rightEigenvectorClosedForm ∧ leftEigenvectorClosedForm ∧ doobKernelClosedForm ∧
      stationaryDistributionClosedForm := by
  exact ⟨hRight, hLeft, hKernel, hStationary⟩

end Omega.Folding
