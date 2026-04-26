import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

universe u

/-- Concrete finite-dimensional matrix-refinement package for
`thm:gm-mellin-meromorphic-fingerprint`.  The zero-translation branches are already
collected into the matrix `zeroBranchMatrix`; the packaged refinement equation is the
finite resolvent system `(I - P(z)) M(z) = H(z)`. -/
structure gm_mellin_meromorphic_fingerprint_data where
  State : Type u
  stateDecEq : DecidableEq State
  stateFintype : Fintype State
  zeroBranchMatrix : ℂ → Matrix State State ℂ
  mellinVector : ℂ → State → ℂ
  holomorphicRemainder : ℂ → State → ℂ
  refinementEquation :
    ∀ z, ((1 : Matrix State State ℂ) - zeroBranchMatrix z).mulVec (mellinVector z) =
      holomorphicRemainder z

namespace gm_mellin_meromorphic_fingerprint_data

/-- The finite matrix `I - P(z)` after moving zero-translation branches left. -/
def resolventMatrix (D : gm_mellin_meromorphic_fingerprint_data) (z : ℂ) :
    Matrix D.State D.State ℂ :=
  letI := D.stateDecEq
  (1 : Matrix D.State D.State ℂ) - D.zeroBranchMatrix z

/-- The determinant certificate controlling the possible finite-dimensional poles. -/
noncomputable def determinantCertificate (D : gm_mellin_meromorphic_fingerprint_data)
    (z : ℂ) : ℂ :=
  letI := D.stateDecEq
  letI := D.stateFintype
  (D.resolventMatrix z).det

/-- The adjugate numerator in Cramer's resolvent formula. -/
noncomputable def adjugateNumerator (D : gm_mellin_meromorphic_fingerprint_data)
    (z : ℂ) : D.State → ℂ :=
  letI := D.stateDecEq
  letI := D.stateFintype
  (D.resolventMatrix z).adjugate.mulVec (D.holomorphicRemainder z)

/-- Algebraic meromorphic-fingerprint statement: after multiplying by the determinant,
the Mellin vector is the adjugate numerator; away from the determinant zero set this gives
the finite matrix resolvent formula. -/
noncomputable def statement (D : gm_mellin_meromorphic_fingerprint_data) : Prop :=
  ∀ z,
    D.determinantCertificate z • D.mellinVector z = D.adjugateNumerator z ∧
      (D.determinantCertificate z ≠ 0 →
        D.mellinVector z = (D.determinantCertificate z)⁻¹ • D.adjugateNumerator z)

end gm_mellin_meromorphic_fingerprint_data

open gm_mellin_meromorphic_fingerprint_data

/-- Paper label: `thm:gm-mellin-meromorphic-fingerprint`.  A finite matrix refinement
equation gives the determinant/adjugate certificate for the Mellin vector, hence the only
possible poles of the resolvent expression are zeros of `det(I - P(z))`. -/
theorem paper_gm_mellin_meromorphic_fingerprint
    (D : gm_mellin_meromorphic_fingerprint_data) :
    D.statement := by
  classical
  letI := D.stateDecEq
  letI := D.stateFintype
  intro z
  let A : Matrix D.State D.State ℂ := D.resolventMatrix z
  have hsystem : A.mulVec (D.mellinVector z) = D.holomorphicRemainder z := by
    simpa [A, resolventMatrix] using D.refinementEquation z
  have hdetA : D.determinantCertificate z = A.det := by
    simp [A, determinantCertificate]
  have hdet :
      D.determinantCertificate z • D.mellinVector z = D.adjugateNumerator z := by
    calc
      D.determinantCertificate z • D.mellinVector z =
          A.det • D.mellinVector z := by
            rw [hdetA]
      _ = (A.det • (1 : Matrix D.State D.State ℂ)).mulVec (D.mellinVector z) := by
            rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (A.adjugate * A).mulVec (D.mellinVector z) := by
            rw [Matrix.adjugate_mul]
      _ = A.adjugate.mulVec (A.mulVec (D.mellinVector z)) := by
            rw [Matrix.mulVec_mulVec]
      _ = D.adjugateNumerator z := by
            rw [hsystem]
            simp [A, adjugateNumerator]
  refine ⟨hdet, ?_⟩
  intro hnonzero
  calc
    D.mellinVector z =
        (D.determinantCertificate z)⁻¹ •
          (D.determinantCertificate z • D.mellinVector z) := by
            ext i
            simp [hnonzero]
    _ = (D.determinantCertificate z)⁻¹ • D.adjugateNumerator z := by
          rw [hdet]

end Omega.SyncKernelRealInput
