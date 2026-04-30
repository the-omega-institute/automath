import Omega.SPG.BoundaryGodelArithmeticHypercubeMedian

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9fa-boundary-godel-median-lipschitz`.
Zeta-facing wrapper for the SPG arithmetic-Hamming boundary Gödel median package. -/
theorem paper_xi_time_part9fa_boundary_godel_median_lipschitz
    (arithmeticHammingIsometry medianFormula boundaryImageIsometric volumeLipschitz : Prop)
    (hIsometry : arithmeticHammingIsometry) (hMedian : medianFormula)
    (hBoundaryImage : boundaryImageIsometric) (hVolume : volumeLipschitz) :
    arithmeticHammingIsometry ∧ medianFormula ∧ boundaryImageIsometric ∧ volumeLipschitz := by
  exact Omega.SPG.paper_spg_boundary_godel_arithmetic_hypercube_median
    arithmeticHammingIsometry medianFormula boundaryImageIsometric volumeLipschitz
    hIsometry hMedian hBoundaryImage hVolume

end Omega.Zeta
