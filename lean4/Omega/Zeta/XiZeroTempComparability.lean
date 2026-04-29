import Omega.POM.ProjTropicalMinmean

namespace Omega.Zeta

open Omega.POM.ProjTropicalMinmeanData

/-- Paper label: `thm:xi-zero-temp-comparability`. This is the Zeta-facing corollary of the
explicit tropical/minimum-mean-cycle identification from the POM layer. -/
theorem paper_xi_zero_temp_comparability (D : Omega.POM.ProjTropicalMinmeanData) :
    D.tropicalCost = D.minMeanCycle := by
  simpa using Omega.POM.paper_pom_proj_tropical_minmean D

end Omega.Zeta
