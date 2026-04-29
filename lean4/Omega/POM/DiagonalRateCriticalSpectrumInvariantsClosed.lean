import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace Omega.POM

open Matrix

/-- The normalized critical-line Laplacian specialized to the symmetric two-state model
`(A, C, w) = (2, 2, (1, 1))`. -/
def pom_diagonal_rate_critical_spectrum_invariants_closed_Lw : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1 / 2 : ℚ), -(1 / 2 : ℚ); -(1 / 2 : ℚ), (1 / 2 : ℚ)]

/-- The audited constant `A` from the critical-line presentation. -/
def pom_diagonal_rate_critical_spectrum_invariants_closed_A : ℚ := 2

/-- The audited normalization constant `C` from the critical-line presentation. -/
def pom_diagonal_rate_critical_spectrum_invariants_closed_C : ℚ := 2

/-- The sum `B(w) = Σ w(x)^(-1/2)` in the symmetric specialization. -/
def pom_diagonal_rate_critical_spectrum_invariants_closed_B : ℚ := 2

/-- The sum `p_{-1}(w) = Σ w(x)^(-1)` in the symmetric specialization. -/
def pom_diagonal_rate_critical_spectrum_invariants_closed_pMinusOne : ℚ := 2

/-- For the two-state Laplacian, the pseudodeterminant is twice any principal cofactor. -/
def pom_diagonal_rate_critical_spectrum_invariants_closed_pseudodeterminant : ℚ :=
  2 * pom_diagonal_rate_critical_spectrum_invariants_closed_Lw 0 0

/-- Paper label: `prop:pom-diagonal-rate-critical-spectrum-invariants-closed`. In the symmetric
two-state critical specialization, the trace, the quadratic trace, and the Laplacian
pseudodeterminant all close to exact rational expressions. -/
theorem paper_pom_diagonal_rate_critical_spectrum_invariants_closed :
    Matrix.trace pom_diagonal_rate_critical_spectrum_invariants_closed_Lw =
        (pom_diagonal_rate_critical_spectrum_invariants_closed_A *
            pom_diagonal_rate_critical_spectrum_invariants_closed_B -
          2) /
          pom_diagonal_rate_critical_spectrum_invariants_closed_C ∧
      Matrix.trace
          (pom_diagonal_rate_critical_spectrum_invariants_closed_Lw *
            pom_diagonal_rate_critical_spectrum_invariants_closed_Lw) =
        (pom_diagonal_rate_critical_spectrum_invariants_closed_A ^ 2 *
            pom_diagonal_rate_critical_spectrum_invariants_closed_pMinusOne -
          2 * pom_diagonal_rate_critical_spectrum_invariants_closed_A *
            pom_diagonal_rate_critical_spectrum_invariants_closed_B +
          4) /
          pom_diagonal_rate_critical_spectrum_invariants_closed_C ^ 2 ∧
      Matrix.det pom_diagonal_rate_critical_spectrum_invariants_closed_Lw = 0 ∧
      pom_diagonal_rate_critical_spectrum_invariants_closed_pseudodeterminant = 1 := by
  have hidem :
      pom_diagonal_rate_critical_spectrum_invariants_closed_Lw *
          pom_diagonal_rate_critical_spectrum_invariants_closed_Lw =
        pom_diagonal_rate_critical_spectrum_invariants_closed_Lw := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pom_diagonal_rate_critical_spectrum_invariants_closed_Lw, Matrix.mul_apply,
        Fin.sum_univ_two] <;> norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [pom_diagonal_rate_critical_spectrum_invariants_closed_Lw,
      pom_diagonal_rate_critical_spectrum_invariants_closed_A,
      pom_diagonal_rate_critical_spectrum_invariants_closed_B,
      pom_diagonal_rate_critical_spectrum_invariants_closed_C, Matrix.trace, Fin.sum_univ_two]
  · rw [hidem]
    norm_num [pom_diagonal_rate_critical_spectrum_invariants_closed_Lw,
      pom_diagonal_rate_critical_spectrum_invariants_closed_A,
      pom_diagonal_rate_critical_spectrum_invariants_closed_B,
      pom_diagonal_rate_critical_spectrum_invariants_closed_C,
      pom_diagonal_rate_critical_spectrum_invariants_closed_pMinusOne,
      Matrix.trace, Fin.sum_univ_two]
  · norm_num [pom_diagonal_rate_critical_spectrum_invariants_closed_Lw, Matrix.det_fin_two]
  · norm_num [pom_diagonal_rate_critical_spectrum_invariants_closed_pseudodeterminant,
      pom_diagonal_rate_critical_spectrum_invariants_closed_Lw]

end Omega.POM
