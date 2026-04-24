import Omega.TypedAddressBiaxialCompletion.RadialInformationProjectionLowerBound

namespace Omega.Conclusion

open Omega.TypedAddressBiaxialCompletion

/-- Paper label: `thm:conclusion-radial-compactification-loglog-secondary-cost`. Instantiating the
typed-address radial-information lower bound at the off-critical radial parameter immediately gives
the advertised logarithmic bit-cost estimate. -/
theorem paper_conclusion_radial_compactification_loglog_secondary_cost (sigma L eps : Real)
    (n : Nat) (hsigma : sigma != 1 / 2) (hL : 1 < L) (heps : 0 < eps)
    (hcert :
      Omega.TypedAddressBiaxialCompletion.xiCertifiedRadialReadout ((2 * sigma - 1) * Real.log L)
        eps n) :
    Real.logb 2 (Omega.TypedAddressBiaxialCompletion.xiJacobianAmplification
      ((2 * sigma - 1) * Real.log L) / eps) <= n := by
  let _ := hsigma
  let _ := hL
  let x : Real := (2 * sigma - 1) * Real.log L
  simpa [x] using paper_xi_radial_information_projection_lower_bound x eps n heps hcert

end Omega.Conclusion
