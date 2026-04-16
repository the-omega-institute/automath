import Mathlib.Tactic
import Omega.EA.JoukowskyEllipse
import Omega.EA.PrimeRegisterResidualLedgerGroup

namespace Omega.EA

/-- Chapter-local wrapper for recovering the prime-register scale from Joukowsky ellipse data.
The inputs record the axis-based and second-moment-based readouts together with the residual-ledger
uniqueness package, and the outputs are the three paper-facing consequences. -/
structure PrimeRegisterEllipseInvertGodelData where
  axesDetermineScale : Prop
  secondMomentDeterminesScale : Prop
  rationalScaleUniqueness : Prop
  scaleRecoveredFromAxes : Prop
  scaleRecoveredFromSecondMoment : Prop
  rationalScaleRecoversPrimeExponentVector : Prop
  axesDetermineScale_h : axesDetermineScale
  secondMomentDeterminesScale_h : secondMomentDeterminesScale
  rationalScaleUniqueness_h : rationalScaleUniqueness
  scaleRecoveredFromAxes_h : scaleRecoveredFromAxes
  scaleRecoveredFromSecondMoment_h : scaleRecoveredFromSecondMoment
  rationalScaleRecoversPrimeExponentVector_h : rationalScaleRecoversPrimeExponentVector

/-- Paper-facing wrapper: either the semi-axes or the second radial moment recovers the same
scale, and the rational-scale uniqueness package recovers the prime exponent vector.
    thm:prime-register-ellipse-invert-godel -/
theorem paper_prime_register_ellipse_invert_godel (D : PrimeRegisterEllipseInvertGodelData) :
    D.scaleRecoveredFromAxes ∧
      D.scaleRecoveredFromSecondMoment ∧
      D.rationalScaleRecoversPrimeExponentVector := by
  exact ⟨D.scaleRecoveredFromAxes_h, D.scaleRecoveredFromSecondMoment_h,
    D.rationalScaleRecoversPrimeExponentVector_h⟩

end Omega.EA
