import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.Tactic
import Omega.POM.A2GutCompletion

namespace Omega.POM

open Matrix

noncomputable section

/-- The interpolating effective kernel `A_eff(α) = U + α • R`. -/
def pom_a2_gut_spectral_splitting_A_eff (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 1;
    0, α, 1;
    2 * α, α, 1]

/-- The explicit characteristic matrix `λ I - A_eff(α)`. -/
def pom_a2_gut_spectral_splitting_char_matrix (α lam : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![lam, 0, -1;
    0, lam - α, -1;
    -(2 * α), -α, lam - 1]

/-- Paper label: `prop:pom-a2-gut-spectral-splitting`. The explicit interpolation between the
unified channel `U` and the audited `A₂` residual `R` has a cubic characteristic determinant that
specializes to the rank-one endpoint `U` at `α = 0` and to the full `A₂` kernel at `α = 1`. -/
def pom_a2_gut_spectral_splitting_statement (α lam : ℝ) : Prop :=
  pom_a2_gut_spectral_splitting_A_eff α =
      pom_a2_gut_completion_U + α • pom_a2_gut_completion_R ∧
    pom_a2_gut_spectral_splitting_char_matrix α lam =
      lam • (1 : Matrix (Fin 3) (Fin 3) ℝ) - pom_a2_gut_spectral_splitting_A_eff α ∧
    Matrix.det (pom_a2_gut_spectral_splitting_char_matrix α lam) =
      lam ^ 3 - (1 + α) * lam ^ 2 - 2 * α * lam + 2 * α ^ 2 ∧
    Matrix.det (pom_a2_gut_spectral_splitting_char_matrix 0 lam) = lam ^ 2 * (lam - 1) ∧
    Matrix.det (pom_a2_gut_spectral_splitting_char_matrix 1 lam) =
      lam ^ 3 - 2 * lam ^ 2 - 2 * lam + 2

lemma pom_a2_gut_spectral_splitting_A_eff_eq (α : ℝ) :
    pom_a2_gut_spectral_splitting_A_eff α =
      pom_a2_gut_completion_U + α • pom_a2_gut_completion_R := by
  ext i j
  fin_cases i
  · fin_cases j <;>
      simp [pom_a2_gut_spectral_splitting_A_eff, pom_a2_gut_completion_U,
        pom_a2_gut_completion_R]
  · fin_cases j <;>
      simp [pom_a2_gut_spectral_splitting_A_eff, pom_a2_gut_completion_U,
        pom_a2_gut_completion_R]
  · fin_cases j <;>
      simp [pom_a2_gut_spectral_splitting_A_eff, pom_a2_gut_completion_U,
        pom_a2_gut_completion_R]
      ; ring

lemma pom_a2_gut_spectral_splitting_char_matrix_eq (α lam : ℝ) :
    pom_a2_gut_spectral_splitting_char_matrix α lam =
      lam • (1 : Matrix (Fin 3) (Fin 3) ℝ) - pom_a2_gut_spectral_splitting_A_eff α := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pom_a2_gut_spectral_splitting_char_matrix, pom_a2_gut_spectral_splitting_A_eff]

lemma pom_a2_gut_spectral_splitting_det (α lam : ℝ) :
    Matrix.det (pom_a2_gut_spectral_splitting_char_matrix α lam) =
      lam ^ 3 - (1 + α) * lam ^ 2 - 2 * α * lam + 2 * α ^ 2 := by
  simp [pom_a2_gut_spectral_splitting_char_matrix, Matrix.det_fin_three]
  ring

theorem paper_pom_a2_gut_spectral_splitting (α : ℝ) («λ» : ℝ) :
    pom_a2_gut_spectral_splitting_statement α «λ» := by
  refine ⟨pom_a2_gut_spectral_splitting_A_eff_eq α,
    pom_a2_gut_spectral_splitting_char_matrix_eq α «λ»,
    pom_a2_gut_spectral_splitting_det α «λ», ?_, ?_⟩
  · have h := pom_a2_gut_spectral_splitting_det 0 «λ»
    nlinarith
  · have h := pom_a2_gut_spectral_splitting_det 1 «λ»
    nlinarith

end

end Omega.POM
