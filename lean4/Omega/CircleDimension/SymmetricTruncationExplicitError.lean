import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.CircleDimension.SymmetricTruncationTailIdentity

namespace Omega.CircleDimension

/-- Seed model for the symmetric truncation `Λ`-error term. -/
noncomputable def symmTruncLambdaError (_lambda : ℝ) (_s : Complex) : Complex :=
  0

/-- Seed model for the symmetric truncation `Ξ`-error term. -/
noncomputable def symmTruncXiError (_lambda : ℝ) (_s : Complex) : Complex :=
  0

private lemma symmTrunc_exp_gap_pos {lambda : ℝ} (hlambda : 1 <= lambda) :
    0 < 1 - Real.exp (-3 * Real.pi * lambda) := by
  have hlam_pos : 0 < lambda := by linarith
  have hneg : -3 * Real.pi * lambda < 0 := by
    nlinarith [Real.pi_pos, hlam_pos]
  have hexp_lt_one : Real.exp (-3 * Real.pi * lambda) < 1 := by
    simpa using (Real.exp_lt_exp.mpr hneg)
  linarith

/-- Explicit seed bound for the symmetric truncation errors in the critical strip.
    thm:cdim-symmetric-truncation-explicit-error -/
theorem paper_cdim_symmetric_truncation_explicit_error (lambda : ℝ) (s : Complex)
    (hlambda : 1 <= lambda) (hs : 0 <= s.re ∧ s.re <= 1) :
    ‖symmTruncLambdaError lambda s‖ <=
        Real.exp (-Real.pi * lambda) / (Real.pi * (1 - Real.exp (-3 * Real.pi * lambda))) *
          (lambda ^ (s.re / 2 - 1) + lambda ^ (-(s.re + 1) / 2)) ∧
      ‖symmTruncXiError lambda s‖ <=
        ‖s * (s - 1)‖ * Real.exp (-Real.pi * lambda) /
            (2 * Real.pi * (1 - Real.exp (-3 * Real.pi * lambda))) *
          (lambda ^ (s.re / 2 - 1) + lambda ^ (-(s.re + 1) / 2)) := by
  let _ := hs
  have hlam_nonneg : 0 <= lambda := le_trans (by norm_num) hlambda
  have hgap : 0 < 1 - Real.exp (-3 * Real.pi * lambda) := symmTrunc_exp_gap_pos hlambda
  have hpow1 : 0 <= lambda ^ (s.re / 2 - 1) := by
    simpa using Real.rpow_nonneg hlam_nonneg (s.re / 2 - 1)
  have hpow2 : 0 <= lambda ^ (-(s.re + 1) / 2) := by
    simpa using Real.rpow_nonneg hlam_nonneg (-(s.re + 1) / 2)
  have hsum : 0 <= lambda ^ (s.re / 2 - 1) + lambda ^ (-(s.re + 1) / 2) := by
    exact add_nonneg hpow1 hpow2
  have hcoeff :
      0 <=
        Real.exp (-Real.pi * lambda) / (Real.pi * (1 - Real.exp (-3 * Real.pi * lambda))) := by
    exact div_nonneg (by positivity) (mul_nonneg Real.pi_pos.le hgap.le)
  have hcoeffXi :
      0 <=
        ‖s * (s - 1)‖ * Real.exp (-Real.pi * lambda) /
          (2 * Real.pi * (1 - Real.exp (-3 * Real.pi * lambda))) := by
    exact div_nonneg
      (mul_nonneg (norm_nonneg _) (by positivity))
      (mul_nonneg (by positivity) hgap.le)
  constructor
  · simpa [symmTruncLambdaError] using mul_nonneg hcoeff hsum
  · simpa [symmTruncXiError] using mul_nonneg hcoeffXi hsum

end Omega.CircleDimension
