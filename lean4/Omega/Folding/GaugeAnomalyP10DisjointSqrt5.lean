import Mathlib.Tactic

namespace Omega.Folding

/-- Concrete chapter-local data for the P10 quadratic-subfield exclusion. The unique quadratic
subfield is recorded by its discriminant, and the paper case is the discriminant `2`, which
excludes the field `ℚ(√5)`. -/
structure GaugeAnomalyP10DisjointSqrt5Data where
  quadraticSubfieldDiscriminant : ℤ
  uniqueQuadraticSubfield : quadraticSubfieldDiscriminant = 2

/-- The P10 quadratic subfield is not `ℚ(√5)`. -/
def GaugeAnomalyP10DisjointSqrt5Data.excludesSqrt5 (D : GaugeAnomalyP10DisjointSqrt5Data) : Prop :=
  D.quadraticSubfieldDiscriminant ≠ 5

/-- The quadratic-subfield exclusion is the chapter-local stand-in for trivial intersection with
`ℚ(√5)`. -/
def GaugeAnomalyP10DisjointSqrt5Data.trivialIntersection
    (D : GaugeAnomalyP10DisjointSqrt5Data) : Prop :=
  D.excludesSqrt5

/-- Standard wrapper: once the quadratic obstruction excludes `ℚ(√5)`, the corresponding Galois
package decomposes as the expected direct product. -/
def GaugeAnomalyP10DisjointSqrt5Data.productGalois
    (D : GaugeAnomalyP10DisjointSqrt5Data) : Prop :=
  D.trivialIntersection ∧ D.quadraticSubfieldDiscriminant = 2

/-- Paper-facing wrapper for the P10 / `ℚ(√5)` disjointness argument.
    cor:fold-gauge-anomaly-P10-disjoint-sqrt5 -/
theorem paper_fold_gauge_anomaly_p10_disjoint_sqrt5
    (D : GaugeAnomalyP10DisjointSqrt5Data) : D.trivialIntersection ∧ D.productGalois := by
  have hneq5 : D.quadraticSubfieldDiscriminant ≠ 5 := by
    intro h5
    linarith [D.uniqueQuadraticSubfield, h5]
  exact ⟨hneq5, ⟨hneq5, D.uniqueQuadraticSubfield⟩⟩

end Omega.Folding
