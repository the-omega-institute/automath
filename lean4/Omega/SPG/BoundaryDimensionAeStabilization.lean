import Omega.SPG.BayesFiniteMistakesSummable
import Omega.SPG.PrefixScanErrorBoundaryDimensionUpper

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for almost-sure eventual stabilization from strict boundary-dimension
    decay: the boundary-growth hypothesis implies summable scan error, and Borel-Cantelli then
    yields eventual stability.
    cor:spg-boundary-dimension-ae-stabilization -/
theorem paper_spg_boundary_dimension_ae_stabilization
    (boundaryDecay summableError eventualStability : Prop)
    (hDecay : boundaryDecay -> summableError)
    (hBC : summableError -> eventualStability) :
    boundaryDecay -> eventualStability := by
  intro hBoundary
  exact hBC (hDecay hBoundary)

end Omega.SPG
