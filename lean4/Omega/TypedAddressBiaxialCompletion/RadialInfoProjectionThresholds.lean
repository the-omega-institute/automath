import Omega.TypedAddressBiaxialCompletion.RadialInformationProjectionLowerBound

namespace Omega.TypedAddressBiaxialCompletion

/-- The absolute and relative certified readout thresholds both inherit the same bit-budget upper
bound from the radial information projection lower bound.
    cor:xi-radial-info-projection-thresholds -/
theorem paper_xi_radial_info_projection_thresholds (x eta : Real) (n : Nat) (hx : x != 0)
    (heta : 0 < eta) (heta1 : eta <= 1) (habs : xiCertifiedRadialReadout x 1 n)
    (hrel : xiCertifiedRadialReadout x (eta * |x|) n) :
    Real.logb 2 (xiJacobianAmplification x) <= n /\
      Real.logb 2 (xiJacobianAmplification x / (eta * |x|)) <= n := by
  have hx' : x ≠ 0 := by simpa using hx
  constructor
  · simpa using paper_xi_radial_information_projection_lower_bound x 1 n (by norm_num) habs
  · have habsx : 0 < |x| := abs_pos.mpr hx'
    have hε : 0 < eta * |x| := mul_pos heta habsx
    exact paper_xi_radial_information_projection_lower_bound x (eta * |x|) n hε hrel

end Omega.TypedAddressBiaxialCompletion
