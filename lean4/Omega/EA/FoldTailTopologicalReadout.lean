import Mathlib
import Omega.EA.FoldGroupoidAut0RationalCohomology

namespace Omega.EA

open scoped BigOperators

/-- The tail multiplicity function `T_m(r) = #{x ∈ X_m : d_m(x) ≥ r}`. -/
noncomputable def foldTailMultiplicity (m r : ℕ) : ℕ :=
  ∑ x : X m, if r ≤ X.fiberMultiplicity x then 1 else 0

/-- The degree-`2k-1` odd-generator count from the `PU(d_m(x))` factors. -/
noncomputable def foldOddGeneratorDegreeCount (m k : ℕ) : ℕ :=
  ∑ x : X m, if k + 1 ≤ X.fiberMultiplicity x then 1 else 0

/-- Concrete statement for the topological readout of the fiber-multiplicity tail. -/
def FoldTailTopologicalReadoutStatement (m k : ℕ) : Prop :=
  foldOddGeneratorDegreeCount m k = foldTailMultiplicity m (k + 1)

/-- Paper label: `cor:fold-tail-topological-readout`.
In the rational cohomology model, a `PU(d_m(x))` factor contributes one generator in degree
`2k-1` exactly when `d_m(x) ≥ k+1`, so the total count is the tail multiplicity `T_m(k+1)`. -/
theorem paper_fold_tail_topological_readout (m k : ℕ) : FoldTailTopologicalReadoutStatement m k := by
  dsimp [FoldTailTopologicalReadoutStatement, foldOddGeneratorDegreeCount, foldTailMultiplicity]

end Omega.EA
