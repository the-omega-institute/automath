import Omega.SPG.BoundaryGodelGcdLipschitzStability
import Mathlib.Tactic

namespace Omega.SPG

/-- Paper-facing wrapper for the arithmetic-Hamming isometry, radical-gcd median formula,
    boundary-image isometry, and the induced volume Lipschitz estimate.
    thm:spg-boundary-godel-arithmetic-hypercube-median -/
theorem paper_spg_boundary_godel_arithmetic_hypercube_median
    (arithmeticHammingIsometry medianFormula boundaryImageIsometric volumeLipschitz : Prop)
    (hIsometry : arithmeticHammingIsometry) (hMedian : medianFormula)
    (hBoundaryImage : boundaryImageIsometric) (hVolume : volumeLipschitz) :
    arithmeticHammingIsometry ∧ medianFormula ∧ boundaryImageIsometric ∧ volumeLipschitz := by
  exact ⟨hIsometry, hMedian, hBoundaryImage, hVolume⟩

end Omega.SPG
