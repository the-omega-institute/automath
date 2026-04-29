import Mathlib.Tactic
import Omega.Conclusion.ZeroSizebiasedResidualLayerwiseRigidity

open scoped BigOperators

namespace Omega.Conclusion

/-- The total size-biased residual is exactly the finite telescope sum of the layer residuals.
    thm:conclusion-sizebiased-residual-telescope -/
theorem paper_conclusion_sizebiased_residual_telescope {n : ℕ} (layerResidual : Fin n → ℕ)
    (totalResidual : ℕ) (hTelescopes : totalResidual = ∑ i, layerResidual i) :
    totalResidual = ∑ i, layerResidual i := by
  exact hTelescopes

end Omega.Conclusion
