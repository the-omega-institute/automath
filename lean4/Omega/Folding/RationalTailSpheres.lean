import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local wrapper for the rational odd-sphere decomposition of the connected continuous
symmetry group. The tail-multiplicity combinatorics reindex the classical `PU(d)` sphere factors
by the counts `N_{>= r}(m)`, after which the rational homotopy product, the exterior cohomology
algebra, and the odd rational homotopy ranks are read off directly. -/
structure RationalTailSpheresData where
  tailMultiplicityCombinatorics : Prop
  oddSphereFactorization : Prop
  rationalHomotopyDecomposition : Prop
  cohomologyDescription : Prop
  homotopyRankDescription : Prop
  tailMultiplicityCombinatorics_h : tailMultiplicityCombinatorics
  reindexOddSphereFactors :
    tailMultiplicityCombinatorics → oddSphereFactorization
  deriveRationalHomotopyDecomposition :
    oddSphereFactorization → rationalHomotopyDecomposition
  deriveCohomologyDescription :
    oddSphereFactorization → cohomologyDescription
  deriveHomotopyRankDescription :
    oddSphereFactorization → homotopyRankDescription

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the tail-count description of the odd rational sphere ladder.
    thm:fold-groupoid-aut0-rational-tail-spheres -/
theorem paper_fold_groupoid_aut0_rational_tail_spheres (D : RationalTailSpheresData) :
    D.rationalHomotopyDecomposition ∧ D.cohomologyDescription ∧ D.homotopyRankDescription := by
  have hOddSpheres : D.oddSphereFactorization :=
    D.reindexOddSphereFactors D.tailMultiplicityCombinatorics_h
  exact ⟨D.deriveRationalHomotopyDecomposition hOddSpheres,
    D.deriveCohomologyDescription hOddSpheres,
    D.deriveHomotopyRankDescription hOddSpheres⟩

end Omega.Folding
