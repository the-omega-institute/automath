import Omega.Folding.FoldBinLastbitSufficientTV

namespace Omega.Zeta

/-- Paper label: `thm:xi-fold-lastbit-asymptotic-sufficiency`.

Expose the existing fold-bin last-bit total-variation package under the Xi theorem label. -/
theorem paper_xi_fold_lastbit_asymptotic_sufficiency
    (D : Omega.Folding.FoldBinLastbitSufficientTVData) :
    D.tvCollapse ∧ D.hasExponentialTilt ∧ D.betaConvergesToLogPhi := by
  exact Omega.Folding.paper_fold_bin_lastbit_sufficient_tv D

end Omega.Zeta
