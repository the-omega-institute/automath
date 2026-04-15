import Omega.POM.StarMomentKernelCompression

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the symmetric-compression theorem in
    `2026_projection_ontological_mathematics_core_tams`.
    thm:symmetric-compression -/
theorem paper_projection_symmetric_compression
    (finiteCollisionKernel histogramQuotient compressedRealization spectralRadiusPreserved
      polynomialDimensionGrowth : Prop)
    (hQuotient : finiteCollisionKernel → histogramQuotient)
    (hRealization : histogramQuotient → compressedRealization)
    (hRadius : compressedRealization → spectralRadiusPreserved)
    (hPoly : compressedRealization → polynomialDimensionGrowth)
    (hKernel : finiteCollisionKernel) :
    histogramQuotient ∧ compressedRealization ∧ spectralRadiusPreserved ∧
      polynomialDimensionGrowth := by
  have hHist : histogramQuotient := hQuotient hKernel
  have hReal : compressedRealization := hRealization hHist
  exact ⟨hHist, hReal, hRadius hReal, hPoly hReal⟩

end Omega.POM
