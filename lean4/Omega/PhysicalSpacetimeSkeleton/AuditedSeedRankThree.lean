import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Omega.PhysicalSpacetimeSkeleton.LocalSpaceQuadraticPositive

namespace Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree

open Matrix

/-- Three nonzero spectral witnesses copied from the audited seed table. -/
noncomputable def auditedSeedEigenvalue₁ : ℝ := 5319833 / 1000000
noncomputable def auditedSeedEigenvalue₂ : ℝ := -534795 / 1000000
noncomputable def auditedSeedEigenvalue₃ : ℝ := -2572421 / 1000000

/-- Minimal audited seed matrix packaging the three nonzero spectral witnesses. -/
noncomputable def auditedSeedMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![auditedSeedEigenvalue₁, auditedSeedEigenvalue₂, auditedSeedEigenvalue₃]

lemma auditedSeedMatrix_det_ne_zero : auditedSeedMatrix.det ≠ 0 := by
  have h₁ : auditedSeedEigenvalue₁ ≠ 0 := by
    norm_num [auditedSeedEigenvalue₁]
  have h₂ : auditedSeedEigenvalue₂ ≠ 0 := by
    norm_num [auditedSeedEigenvalue₂]
  have h₃ : auditedSeedEigenvalue₃ ≠ 0 := by
    norm_num [auditedSeedEigenvalue₃]
  simpa [auditedSeedMatrix, Matrix.det_diagonal, Fin.prod_univ_three,
    auditedSeedEigenvalue₁, auditedSeedEigenvalue₂, auditedSeedEigenvalue₃] using
    mul_ne_zero (mul_ne_zero h₁ h₂) h₃

lemma auditedSeedMatrix_isUnit : IsUnit auditedSeedMatrix := by
  exact
    (Matrix.isUnit_iff_isUnit_det (A := auditedSeedMatrix)).2
      (isUnit_iff_ne_zero.mpr auditedSeedMatrix_det_ne_zero)

lemma auditedSeedMatrix_mulVec_injective : Function.Injective auditedSeedMatrix.mulVec := by
  exact Matrix.mulVec_injective_iff_isUnit.2 auditedSeedMatrix_isUnit

/-- The audited seed matrix has full `3 × 3` rank because its determinant is nonzero.
    prop:physical-spacetime-audited-seed-rank-three -/
theorem paper_physical_spacetime_audited_seed_rank_three :
    auditedSeedMatrix.rank = 3 := by
  simpa using Matrix.rank_of_isUnit auditedSeedMatrix auditedSeedMatrix_isUnit

/-- The local quadratic positivity package can now be applied directly to the audited seed matrix. -/
theorem paper_physical_spacetime_audited_seed_local_space_quadratic_positive
    (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    0 < dotProduct v ((auditedSeedMatrix.transpose * auditedSeedMatrix).mulVec v) := by
  exact
    Omega.PhysicalSpacetimeSkeleton.LocalSpaceQuadraticPositive.paper_physical_spacetime_local_space_quadratic_positive_seeds
      auditedSeedMatrix auditedSeedMatrix_mulVec_injective v hv

end Omega.PhysicalSpacetimeSkeleton.AuditedSeedRankThree
