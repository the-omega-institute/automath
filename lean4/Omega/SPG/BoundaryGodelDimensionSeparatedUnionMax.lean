import Mathlib.Tactic

namespace Omega.SPG

/-- Paper-facing separated-union max law for boundary Gödel dimension: if both components
    inject their lower bounds into the separated union and the union already satisfies the
    expected upper bound by the maximum component dimension, then equality follows.
    prop:spg-boundary-godel-dimension-separated-union-max -/
theorem paper_spg_boundary_godel_dimension_separated_union_max
    (dA dB dUnion : ℝ) (hLowerA : dA ≤ dUnion) (hLowerB : dB ≤ dUnion)
    (hUpper : dUnion ≤ max dA dB) :
    dUnion = max dA dB := by
  apply le_antisymm hUpper
  exact max_le_iff.mpr ⟨hLowerA, hLowerB⟩

end Omega.SPG
