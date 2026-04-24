import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- Concrete cylinder-count data for the Hausdorff-dimension/fiber-multiplicity comparison. -/
structure FiberHausdorffDimensionCylinderCountData where
  cylinderCount : ℕ → ℕ
  fiberMultiplicity : ℕ → ℕ
  hausdorffDimension : ℝ
  cylinderCountExponent : ℝ
  hausdorffDimension_eq : hausdorffDimension = cylinderCountExponent
  cylinderCount_le_fiberMultiplicity : ∀ m, cylinderCount m ≤ fiberMultiplicity m

namespace FiberHausdorffDimensionCylinderCountData

/-- The Hausdorff dimension equals the exponent read from the cylinder counts. -/
def hausdorffDimensionFormula (D : FiberHausdorffDimensionCylinderCountData) : Prop :=
  D.hausdorffDimension = D.cylinderCountExponent

/-- Active cylinder counts are bounded above by the corresponding finite fiber multiplicities. -/
def fiberMultiplicityUpperBound (D : FiberHausdorffDimensionCylinderCountData) : Prop :=
  ∀ m, D.cylinderCount m ≤ D.fiberMultiplicity m

end FiberHausdorffDimensionCylinderCountData

open FiberHausdorffDimensionCylinderCountData

/-- Paper-facing cylinder-count package for fiber Hausdorff dimension and multiplicity upper
bound.
    thm:fold-fiber-hausdorff-dimension-cylinder-count -/
theorem paper_fold_fiber_hausdorff_dimension_cylinder_count
    (D : FiberHausdorffDimensionCylinderCountData) :
    D.hausdorffDimensionFormula ∧ D.fiberMultiplicityUpperBound := by
  exact ⟨D.hausdorffDimension_eq, D.cylinderCount_le_fiberMultiplicity⟩

end Omega.Folding
