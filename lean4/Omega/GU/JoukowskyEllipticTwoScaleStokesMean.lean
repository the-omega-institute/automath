import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Omega.GU.JoukowskyGodelPullbackFactorization

namespace Omega.GU

open Omega.GU.LeyangHolographicN2

/-- Logarithmic mean of the pulled-back elliptic kernel along the Joukowsky parameter. -/
noncomputable def joukowskyEllipseTwoScaleStokesMean (r z z₁ z₂ : ℂ) : ℝ :=
  Real.log ‖Q_r_eval_at_J r z z₁ z₂ * (r ^ 2 * z ^ 2)‖ / 2

/-- Logarithmic mean split into the direct polynomial factor and the reciprocal factor. -/
noncomputable def circleFactorLogMean (r z z₁ z₂ : ℂ) : ℝ :=
  (Real.log ‖P z z₁ z₂‖ + Real.log ‖quadraticReciprocalEval (r ^ 2 * z) z₁ z₂‖) / 2

/-- The Joukowsky pullback factors the elliptic logarithmic mean into the sum of the circle-side
means of `P` and its reciprocal companion.
    thm:group-jg-elliptic-two-scale-stokes-mean -/
theorem paper_group_jg_elliptic_two_scale_stokes_mean
    (r z z₁ z₂ : ℂ) (hr : r ≠ 0) (hz : z ≠ 0) (hP : P z z₁ z₂ ≠ 0)
    (hR : quadraticReciprocalEval (r ^ 2 * z) z₁ z₂ ≠ 0) :
    joukowskyEllipseTwoScaleStokesMean r z z₁ z₂ = circleFactorLogMean r z z₁ z₂ := by
  unfold joukowskyEllipseTwoScaleStokesMean circleFactorLogMean
  rw [paper_group_jg_pullback_factorization r z z₁ z₂ hr hz]
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hP) (norm_ne_zero_iff.mpr hR)]

end Omega.GU
