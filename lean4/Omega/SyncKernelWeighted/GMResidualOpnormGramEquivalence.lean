import Mathlib.Data.Real.Basic

namespace Omega.SyncKernelWeighted

/-- Lower comparison between the residual operator norm and the finite-dimensional Gram
certificate. -/
def gm_residual_opnorm_gram_equivalence_lower_statement
    (residualOpNorm gramOpNorm M lowerConstant : ℝ) : Prop :=
  lowerConstant * M ^ (4 : ℕ) * gramOpNorm ≤ residualOpNorm ^ (2 : ℕ)

/-- Upper comparison between the residual operator norm and the finite-dimensional Gram
certificate. -/
def gm_residual_opnorm_gram_equivalence_upper_statement
    (residualOpNorm gramOpNorm M upperConstant : ℝ) : Prop :=
  residualOpNorm ^ (2 : ℕ) ≤ upperConstant * M ^ (4 : ℕ) * gramOpNorm

/-- Concrete data package for the two-sided `M^4` equivalence between the residual norm and the
Gram-matrix operator norm. -/
structure gm_residual_opnorm_gram_equivalence_data where
  gm_residual_opnorm_gram_equivalence_residual_opnorm : ℝ
  gm_residual_opnorm_gram_equivalence_gram_opnorm : ℝ
  gm_residual_opnorm_gram_equivalence_scale_M : ℝ
  gm_residual_opnorm_gram_equivalence_lower_constant : ℝ
  gm_residual_opnorm_gram_equivalence_upper_constant : ℝ
  gm_residual_opnorm_gram_equivalence_lower_bound :
    gm_residual_opnorm_gram_equivalence_lower_statement
      gm_residual_opnorm_gram_equivalence_residual_opnorm
      gm_residual_opnorm_gram_equivalence_gram_opnorm
      gm_residual_opnorm_gram_equivalence_scale_M
      gm_residual_opnorm_gram_equivalence_lower_constant
  gm_residual_opnorm_gram_equivalence_upper_bound :
    gm_residual_opnorm_gram_equivalence_upper_statement
      gm_residual_opnorm_gram_equivalence_residual_opnorm
      gm_residual_opnorm_gram_equivalence_gram_opnorm
      gm_residual_opnorm_gram_equivalence_scale_M
      gm_residual_opnorm_gram_equivalence_upper_constant

namespace gm_residual_opnorm_gram_equivalence_data

/-- The packaged two-sided equivalence between the residual operator norm and the Gram spectral
certificate. -/
def statement (D : gm_residual_opnorm_gram_equivalence_data) : Prop :=
  gm_residual_opnorm_gram_equivalence_lower_statement
      D.gm_residual_opnorm_gram_equivalence_residual_opnorm
      D.gm_residual_opnorm_gram_equivalence_gram_opnorm
      D.gm_residual_opnorm_gram_equivalence_scale_M
      D.gm_residual_opnorm_gram_equivalence_lower_constant ∧
    gm_residual_opnorm_gram_equivalence_upper_statement
      D.gm_residual_opnorm_gram_equivalence_residual_opnorm
      D.gm_residual_opnorm_gram_equivalence_gram_opnorm
      D.gm_residual_opnorm_gram_equivalence_scale_M
      D.gm_residual_opnorm_gram_equivalence_upper_constant

end gm_residual_opnorm_gram_equivalence_data

open gm_residual_opnorm_gram_equivalence_data

/-- Paper label: `thm:gm-residual-opnorm-gram-equivalence`. -/
theorem paper_gm_residual_opnorm_gram_equivalence
    (D : gm_residual_opnorm_gram_equivalence_data) : D.statement := by
  exact ⟨D.gm_residual_opnorm_gram_equivalence_lower_bound,
    D.gm_residual_opnorm_gram_equivalence_upper_bound⟩

end Omega.SyncKernelWeighted
