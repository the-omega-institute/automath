import Mathlib.Tactic

namespace Omega.Experiments

/-- Chapter-local package for the standard KL-from-TV estimate under a positive minimum `q`-atom.
The data records the shared-support / minimum-atom hypotheses, the intermediate
`χ²`-bound extracted from the `ℓ¹` distance, the logarithmic KL-vs-`χ²` comparison, and the
final rewrite from `‖p-q‖₁ = 2 D_{TV}(p,q)` to the quadratic TV certificate. -/
structure KLFromTVQminData where
  sharedSupport : Prop
  qMinPositive : Prop
  chiSqControlledByL1 : Prop
  klLeLogOnePlusChiSq : Prop
  l1EqualsTwoTv : Prop
  logChiSqBound : Prop
  tvQuadraticBound : Prop
  sharedSupport_h : sharedSupport
  qMinPositive_h : qMinPositive
  klLeLogOnePlusChiSq_h : klLeLogOnePlusChiSq
  l1EqualsTwoTv_h : l1EqualsTwoTv
  deriveChiSqControlledByL1 : sharedSupport → qMinPositive → chiSqControlledByL1
  deriveLogChiSqBound : chiSqControlledByL1 → klLeLogOnePlusChiSq → logChiSqBound
  deriveTvQuadraticBound : logChiSqBound → l1EqualsTwoTv → tvQuadraticBound

/-- Paper-facing wrapper for the explicit KL certificate obtained from a total-variation estimate
and a positive minimum atom of the reference law.
    lem:kl-from-tv-qmin -/
theorem paper_kl_from_tv_qmin (data : KLFromTVQminData) :
    data.logChiSqBound ∧ data.tvQuadraticBound := by
  have hChiSq : data.chiSqControlledByL1 :=
    data.deriveChiSqControlledByL1 data.sharedSupport_h data.qMinPositive_h
  have hLog : data.logChiSqBound := data.deriveLogChiSqBound hChiSq data.klLeLogOnePlusChiSq_h
  exact ⟨hLog, data.deriveTvQuadraticBound hLog data.l1EqualsTwoTv_h⟩

end Omega.Experiments
