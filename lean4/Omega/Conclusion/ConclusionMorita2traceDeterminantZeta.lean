import Mathlib

namespace Omega.Conclusion

open Matrix

/-- Graded-dimension matrix of the two-object Morita seed family. -/
noncomputable def conclusion_morita_2trace_determinant_zeta_gradedMatrix (d : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal d

/-- Diagonal component of the `n`-fold tensor power over `B`. -/
noncomputable def conclusion_morita_2trace_determinant_zeta_tensorDiagonal
    (d : Fin 2 → ℝ) (n : ℕ) (i : Fin 2) : ℝ :=
  (conclusion_morita_2trace_determinant_zeta_gradedMatrix d ^ n) i i

/-- Morita 2-trace in the seed model is ordinary matrix trace. -/
noncomputable def conclusion_morita_2trace_determinant_zeta_moritaTwoTrace
    (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Matrix.trace A

/-- Determinant-zeta seed of the two-object Morita model. -/
noncomputable def conclusion_morita_2trace_determinant_zeta_logDet (d : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  -Real.log (Matrix.det (1 - t • conclusion_morita_2trace_determinant_zeta_gradedMatrix d))

/-- Paper label: `prop:conclusion-morita-2trace-determinant-zeta`.
For the diagonal graded-dimension seed, tensor powers over `B` are diagonal matrix powers, the
Morita 2-trace is the ordinary trace, and the determinant zeta is the logarithm of the product of
the diagonal Fredholm factors. -/
theorem paper_conclusion_morita_2trace_determinant_zeta (d : Fin 2 → ℝ) (n : ℕ) (t : ℝ) :
    (∀ i : Fin 2,
        conclusion_morita_2trace_determinant_zeta_tensorDiagonal d n i = (d i) ^ n) ∧
      conclusion_morita_2trace_determinant_zeta_moritaTwoTrace
          (conclusion_morita_2trace_determinant_zeta_gradedMatrix d ^ n) =
        (d 0) ^ n + (d 1) ^ n ∧
      conclusion_morita_2trace_determinant_zeta_logDet d t =
        -Real.log ((1 - t * d 0) * (1 - t * d 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp [conclusion_morita_2trace_determinant_zeta_tensorDiagonal,
      conclusion_morita_2trace_determinant_zeta_gradedMatrix, Matrix.diagonal_pow]
  · rw [conclusion_morita_2trace_determinant_zeta_moritaTwoTrace, Matrix.trace_fin_two]
    simp [conclusion_morita_2trace_determinant_zeta_gradedMatrix, Matrix.diagonal_pow]
  · have hdiag :
        1 - t • conclusion_morita_2trace_determinant_zeta_gradedMatrix d =
          Matrix.diagonal (fun i => 1 - t * d i) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [conclusion_morita_2trace_determinant_zeta_gradedMatrix]
      · simp [conclusion_morita_2trace_determinant_zeta_gradedMatrix, hij]
    rw [conclusion_morita_2trace_determinant_zeta_logDet, hdiag, Matrix.det_diagonal, Fin.prod_univ_two]

end Omega.Conclusion
