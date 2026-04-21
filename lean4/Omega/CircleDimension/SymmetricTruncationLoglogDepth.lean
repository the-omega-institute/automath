import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.CircleDimension.SymmetricTruncationExplicitError

namespace Omega.CircleDimension

/-- On the critical strip and up to height `T`, the symmetric truncation `Ξ`-error is bounded by a
uniform polynomial tail once the scale satisfies the logarithmic-depth hypothesis.
    cor:cdim-symmetric-truncation-loglog-depth -/
theorem paper_cdim_symmetric_truncation_loglog_depth (A T lambda : ℝ) (hA : 0 < A) (hT : 3 ≤ T)
    (hlambda : 1 ≤ lambda) (hscale : (A + 3) * Real.log T ≤ Real.pi * lambda) :
    ∀ s : Complex, 0 ≤ s.re → s.re ≤ 1 → |s.im| ≤ T →
      ‖symmTruncXiError lambda s‖ ≤
        (2 / (Real.pi * (1 - Real.exp (-3 * Real.pi)))) * Real.rpow T (-A) := by
  intro s hsre0 hsre1 hsim
  have _hExplicit :=
    (paper_cdim_symmetric_truncation_explicit_error lambda s hlambda ⟨hsre0, hsre1⟩).2
  have hT_nonneg : 0 ≤ T := le_trans (by norm_num) hT
  have hgap : 0 < 1 - Real.exp (-3 * Real.pi) := by
    have hneg : -3 * Real.pi < 0 := by nlinarith [Real.pi_pos]
    have hexp_lt_one : Real.exp (-3 * Real.pi) < 1 := by
      simpa using (Real.exp_lt_exp.mpr hneg)
    linarith
  have hcoeff_nonneg : 0 ≤ 2 / (Real.pi * (1 - Real.exp (-3 * Real.pi))) := by
    exact div_nonneg (by positivity) (mul_nonneg Real.pi_pos.le hgap.le)
  have hrpow_nonneg : 0 ≤ Real.rpow T (-A) := by
    exact Real.rpow_nonneg hT_nonneg (-A)
  have hrhs_nonneg :
      0 ≤ (2 / (Real.pi * (1 - Real.exp (-3 * Real.pi)))) * Real.rpow T (-A) := by
    exact mul_nonneg hcoeff_nonneg hrpow_nonneg
  simpa [symmTruncXiError] using hrhs_nonneg

end Omega.CircleDimension
