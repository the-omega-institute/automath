import Mathlib.Tactic

namespace Omega.POM

/-- Paper-facing wrapper for the median/partial-cube/CAT(0) package of the fiber reconstruction
graph together with its bipartite parity grading.
    cor:pom-fiber-reconstruction-median-partialcube-cat0 -/
theorem paper_pom_fiber_reconstruction_median_partialcube_cat0
    (fiberGraphIsMedian fiberGraphIsPartialCube fiberGraphHasCat0CubeComplex
      fiberGraphIsBipartite fiberGraphHasParityBigrading : Prop)
    (hmedian : fiberGraphIsMedian)
    (hpartial : fiberGraphIsPartialCube)
    (hcat0 : fiberGraphHasCat0CubeComplex)
    (hbip : fiberGraphIsBipartite)
    (hpar : fiberGraphHasParityBigrading) :
    fiberGraphIsMedian ∧ fiberGraphIsPartialCube ∧ fiberGraphHasCat0CubeComplex ∧
      fiberGraphIsBipartite ∧ fiberGraphHasParityBigrading := by
  exact ⟨hmedian, hpartial, hcat0, hbip, hpar⟩

end Omega.POM
