import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

abbrev gm_centered_trace3_energy_variance_matrix := Matrix (Fin 3) (Fin 3) ℝ

/-- Concrete `3 × 3` Gram package used for the centered trace-`3` identity. -/
def gm_centered_trace3_energy_variance_gram (x y z : ℝ) :
    gm_centered_trace3_energy_variance_matrix :=
  Matrix.diagonal ![x, y, z]

/-- Mean trace density of the concrete `3 × 3` Gram package. -/
def gm_centered_trace3_energy_variance_mean (x y z : ℝ) : ℝ :=
  (x + y + z) / 3

/-- Variance-style correction recorded after removing the centered scalar channel. -/
def gm_centered_trace3_energy_variance_variance (x y z : ℝ) : ℝ :=
  let μ := gm_centered_trace3_energy_variance_mean x y z
  (x - μ) ^ 2 + (y - μ) ^ 2 + (z - μ) ^ 2

private lemma gm_centered_trace3_energy_variance_gram_pow_three (x y z : ℝ) :
    gm_centered_trace3_energy_variance_gram x y z ^ 3 = Matrix.diagonal ![x ^ 3, y ^ 3, z ^ 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gm_centered_trace3_energy_variance_gram, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

private lemma gm_centered_trace3_energy_variance_trace_cube (x y z : ℝ) :
    Matrix.trace (gm_centered_trace3_energy_variance_gram x y z ^ 3) = x ^ 3 + y ^ 3 + z ^ 3 := by
  rw [gm_centered_trace3_energy_variance_gram_pow_three]
  rw [Matrix.trace_fin_three]
  simp

private lemma gm_centered_trace3_energy_variance_centered_pow_three (x y z : ℝ) :
    let μ := gm_centered_trace3_energy_variance_mean x y z
    (gm_centered_trace3_energy_variance_gram x y z -
        μ • (1 : gm_centered_trace3_energy_variance_matrix)) ^ 3 =
      Matrix.diagonal ![(x - μ) ^ 3, (y - μ) ^ 3, (z - μ) ^ 3] := by
  dsimp [gm_centered_trace3_energy_variance_mean]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gm_centered_trace3_energy_variance_gram, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

private lemma gm_centered_trace3_energy_variance_trace_centered_cube (x y z : ℝ) :
    let μ := gm_centered_trace3_energy_variance_mean x y z
    Matrix.trace ((gm_centered_trace3_energy_variance_gram x y z -
          μ • (1 : gm_centered_trace3_energy_variance_matrix)) ^ 3) =
      (x - μ) ^ 3 + (y - μ) ^ 3 + (z - μ) ^ 3 := by
  dsimp
  rw [gm_centered_trace3_energy_variance_centered_pow_three]
  rw [Matrix.trace_fin_three]
  simp

/-- Chapter-local centered trace-`3` package: for the explicit diagonal `3 × 3` Gram matrix, the
cube of the centered matrix is governed by the raw cubic trace together with the centered
variance-style correction. -/
def gm_centered_trace3_energy_variance_statement : Prop :=
  ∀ x y z : ℝ,
    let G := gm_centered_trace3_energy_variance_gram x y z
    let μ := gm_centered_trace3_energy_variance_mean x y z
    let variance := gm_centered_trace3_energy_variance_variance x y z
    Matrix.trace ((G - μ • (1 : gm_centered_trace3_energy_variance_matrix)) ^ 3) =
      Matrix.trace (G ^ 3) - 3 * μ * variance - 3 * μ ^ 3

/-- Paper label: `prop:gm-centered-trace3-energy-variance`. Centering the explicit diagonal
`3 × 3` Gram package removes the scalar channel from the third trace moment; the remaining cubic
trace is the raw cubic moment corrected by the centered variance term and the residual `-3 μ^3`
contribution. -/
theorem paper_gm_centered_trace3_energy_variance :
    gm_centered_trace3_energy_variance_statement := by
  intro x y z
  dsimp
  rw [gm_centered_trace3_energy_variance_trace_centered_cube,
    gm_centered_trace3_energy_variance_trace_cube]
  let μ : ℝ := gm_centered_trace3_energy_variance_mean x y z
  have hμ : x + y + z = 3 * μ := by
    dsimp [μ, gm_centered_trace3_energy_variance_mean]
    field_simp
  have hvariance :
      gm_centered_trace3_energy_variance_variance x y z =
        (x - μ) ^ 2 + (y - μ) ^ 2 + (z - μ) ^ 2 := by
    dsimp [gm_centered_trace3_energy_variance_variance, μ]
  rw [hvariance]
  ring_nf
  nlinarith [hμ]

end

end Omega.SyncKernelWeighted
