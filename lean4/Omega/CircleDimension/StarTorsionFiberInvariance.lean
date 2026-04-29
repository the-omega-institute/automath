import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

/-- Paper label: `thm:cdim-star-torsion-fiber-invariance`.
In the bookkeeping model for Pontryagin dual connected components, adjoining an additional torsion
fiber leaves both the circle dimension and the normalized half-circle dimension unchanged. -/
theorem paper_cdim_star_torsion_fiber_invariance (freeRank torsion fiber : ℕ) :
    circleDim freeRank (torsion + fiber) = circleDim freeRank torsion ∧
      halfCircleDim freeRank (torsion + fiber) = halfCircleDim freeRank torsion := by
  refine ⟨circleDim_finite_extension freeRank (torsion + fiber) torsion, ?_⟩
  simp [halfCircleDim, circleDim]

end Omega.CircleDimension
