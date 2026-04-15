import Omega.Topos.IntrinsicHiddenStateLowerBound

namespace Omega.Topos

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the conservative recovery budget corollary.
    cor:conservative-recovery-budget -/
theorem paper_conservative_extension_conservative_recovery_budget
    (finiteObstructionPresentation visibleQuotientUnchanged conservativeEnrichment
      fullResolution auxiliaryStrictificationCode hiddenStateBudget : Prop)
    (hCode :
      finiteObstructionPresentation →
        visibleQuotientUnchanged →
          conservativeEnrichment →
            fullResolution →
              auxiliaryStrictificationCode)
    (hBudget : auxiliaryStrictificationCode → hiddenStateBudget) :
    finiteObstructionPresentation →
      visibleQuotientUnchanged →
        conservativeEnrichment →
          fullResolution → hiddenStateBudget := by
  intro hFinite hVisible hConservative hResolution
  exact hBudget (hCode hFinite hVisible hConservative hResolution)

end Omega.Topos
