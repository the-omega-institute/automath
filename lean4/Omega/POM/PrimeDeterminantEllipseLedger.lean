import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Omega.POM.PrimeDeterminantEllipseLedger

open Matrix Finset

/-- Encoding matrix `[[b·N+p, b], [N, 1]]`.
    cor:pom-prime-determinant-ellipse-ledger -/
def encodingMatrix (b N p : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![b * N + p, b; N, 1]

/-- `det(encodingMatrix b N p) = p`.
    cor:pom-prime-determinant-ellipse-ledger -/
theorem det_encodingMatrix (b N p : ℤ) :
    (encodingMatrix b N p).det = p := by
  simp [encodingMatrix, Matrix.det_fin_two]

/-- Product formula: `det(M₁ * M₂) = det M₁ * det M₂` applied to encoding matrices.
    cor:pom-prime-determinant-ellipse-ledger -/
theorem det_encodingMatrix_mul (b₁ b₂ N p₁ p₂ : ℤ) :
    (encodingMatrix b₁ N p₁ * encodingMatrix b₂ N p₂).det = p₁ * p₂ := by
  rw [Matrix.det_mul, det_encodingMatrix, det_encodingMatrix]

/-- Paper package: det product formula for a list of encoding matrices.
    cor:pom-prime-determinant-ellipse-ledger -/
theorem paper_pom_prime_determinant_ellipse_ledger
    (ms : List (ℤ × ℤ)) (N : ℤ) :
    (ms.map (fun bp => encodingMatrix bp.1 N bp.2)).prod.det =
      (ms.map (fun bp => bp.2)).prod := by
  induction ms with
  | nil => simp [Matrix.det_one]
  | cons hd tl ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [Matrix.det_mul, ih, det_encodingMatrix]

end Omega.POM.PrimeDeterminantEllipseLedger
