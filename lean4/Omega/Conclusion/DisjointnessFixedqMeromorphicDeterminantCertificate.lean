import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Omega.Conclusion.DisjointnessFixedqSymmetricKrylovSector

namespace Omega.Conclusion

open ConclusionDisjointnessFixedqSymmetricKrylovSectorData

/-- Paper label: `cor:conclusion-disjointness-fixedq-meromorphic-determinant-certificate`.
After the fixed-`q` Krylov compression, the exceptional spectrum is monitored by a determinant on
the `q + 1` dimensional compressed sector, and the determinant lemma reduces it to a fixed-size
certificate. -/
theorem paper_conclusion_disjointness_fixedq_meromorphic_determinant_certificate
    (D : ConclusionDisjointnessFixedqSymmetricKrylovSectorData) :
    D.fixedqSymmetricKrylovSector ∧
      ∀ A B : Matrix (Fin (D.q + 1)) (Fin (D.q + 1)) ℝ,
        Matrix.det (1 + A * B) = Matrix.det (1 + B * A) := by
  refine ⟨paper_conclusion_disjointness_fixedq_symmetric_krylov_sector D, ?_⟩
  intro A B
  simpa [add_comm] using Matrix.det_one_add_mul_comm A B

end Omega.Conclusion
