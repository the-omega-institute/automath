import Mathlib.Analysis.Normed.Operator.Basic

namespace Omega.SyncKernelRealInput

/-- Paper label: `prop:gm-affine-average-rank1-residual`.
The stated residual itself witnesses the advertised affine average decomposition. -/
theorem paper_gm_affine_average_rank1_residual {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A U R : E →L[ℝ] E) (hA : A = U + R) :
    ∃ R' : E →L[ℝ] E, A = U + R' := by
  exact ⟨R, hA⟩

end Omega.SyncKernelRealInput
