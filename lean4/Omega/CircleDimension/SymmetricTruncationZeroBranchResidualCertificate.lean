import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.CircleDimension.SymmetricTruncationLoglogDepth
import Omega.CircleDimension.SymmetricTruncationMultiplicativeRecursionGenerator

namespace Omega.CircleDimension

noncomputable section

structure cdim_symmetric_truncation_zero_branch_residual_certificate_data where
  A : ℝ
  T : ℝ
  lambda : ℝ

def cdim_symmetric_truncation_zero_branch_residual_certificate_branch_residual
    (lambda : ℝ) : ℂ :=
  circleDimensionSymmetricScaleRecursion 1 lambda (1 / 2 : ℂ)

def cdim_symmetric_truncation_zero_branch_residual_certificate_stmt
    (D : cdim_symmetric_truncation_zero_branch_residual_certificate_data) : Prop :=
  cdim_symmetric_truncation_zero_branch_residual_certificate_branch_residual D.lambda = 0 ∧
    HasDerivAt (fun r => circleDimensionSymmetricCore (Real.exp r) (1 / 2 : ℂ)) 0
      (Real.log D.lambda) ∧
    (0 < D.A → 3 ≤ D.T → 1 ≤ D.lambda → (D.A + 3) * Real.log D.T ≤ Real.pi * D.lambda →
      ∀ s : Complex, 0 ≤ s.re → s.re ≤ 1 → |s.im| ≤ D.T →
        ‖symmTruncXiError D.lambda s‖ ≤
          (2 / (Real.pi * (1 - Real.exp (-3 * Real.pi)))) * Real.rpow D.T (-D.A))

/-- Paper label: `cor:cdim-symmetric-truncation-zero-branch-residual-certificate`. The explicit
self-dual branch has zero residual at `s = 1 / 2`, its logarithmic flow has zero derivative there,
and the already formalized truncation estimate gives the residual certificate on the critical strip
under the standard scale hypotheses. -/
theorem paper_cdim_symmetric_truncation_zero_branch_residual_certificate
    (D : cdim_symmetric_truncation_zero_branch_residual_certificate_data) :
    cdim_symmetric_truncation_zero_branch_residual_certificate_stmt D := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [cdim_symmetric_truncation_zero_branch_residual_certificate_branch_residual] using
      (paper_circle_dimension_symmetric_truncation_multiplicative_recursion_generator 1 D.lambda
        (1 / 2 : ℂ)).1
  · simpa [circleDimensionSymmetricLogGenerator] using
      (paper_circle_dimension_symmetric_truncation_multiplicative_recursion_generator 1 D.lambda
        (1 / 2 : ℂ)).2
  · intro hA hT hlambda hscale s hsre0 hsre1 hsim
    exact paper_cdim_symmetric_truncation_loglog_depth D.A D.T D.lambda hA hT hlambda hscale s
      hsre0 hsre1 hsim

end

end Omega.CircleDimension
