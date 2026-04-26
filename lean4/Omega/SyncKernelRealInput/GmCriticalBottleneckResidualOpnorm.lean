import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Paper label: `thm:gm-critical-bottleneck-residual-opnorm`.  The paper-facing bottleneck
package is exactly the assumed equivalence between critical-window improvement and the residual
operator-norm gap. -/
theorem paper_gm_critical_bottleneck_residual_opnorm
    (criticalWindowImproves residualOpnormGap : Prop)
    (h : criticalWindowImproves ↔ residualOpnormGap) :
    criticalWindowImproves ↔ residualOpnormGap := by
  exact h

end Omega.SyncKernelRealInput
