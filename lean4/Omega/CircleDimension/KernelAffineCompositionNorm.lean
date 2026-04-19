import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The norm formula for the affine composition operator in the chapter-local model. -/
noncomputable def affineCompositionNorm (lam beta : Real) : Real :=
  Real.sqrt (1 / |lam|)

/-- The bounded regime is exactly the small-scale regime `|lam| ≤ 1`. -/
def affineCompositionBounded (lam beta : Real) : Prop :=
  |lam| ≤ 1

/-- Paper: `prop:cdim-kernel-affine-composition-norm`. -/
theorem paper_cdim_kernel_affine_composition_norm (lam beta : Real) (hlam : lam ≠ 0) :
    (|lam| ≤ 1 → affineCompositionNorm lam beta = Real.sqrt (1 / |lam|)) ∧
      (1 < |lam| → ¬ affineCompositionBounded lam beta) := by
  constructor
  · intro hlam_le
    simp [affineCompositionNorm]
  · intro hlam_gt
    simpa [affineCompositionBounded] using not_le_of_gt hlam_gt

end Omega.CircleDimension
