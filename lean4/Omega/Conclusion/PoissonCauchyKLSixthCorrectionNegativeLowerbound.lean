import Omega.CircleDimension.PoissonEntropyTomography
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-poisson-cauchy-kl-sixth-correction-negative-lowerbound`. -/
theorem paper_conclusion_poisson_cauchy_kl_sixth_correction_negative_lowerbound
    {sigma mu3 mu4 C6 : Real}
    (hsigma : 0 < sigma)
    (hpearson : mu3 ^ 2 <= sigma ^ 2 * (mu4 - sigma ^ 4))
    (hC6 :
      C6 = -((sigma ^ 6) / 64 - (sigma ^ 2 * mu4) / 8 + (3 * mu3 ^ 2) / 32)) :
    0 < C6 ∧ (7 * sigma ^ 6 + 2 * mu3 ^ 2) / 64 <= C6 := by
  have hcoeff :=
    Omega.CircleDimension.paper_cdim_poisson_kl_sixth_order_coefficient_negative
      hsigma hpearson
  have hC6mul : 64 * C6 = -(sigma ^ 6 + 6 * mu3 ^ 2 - 8 * sigma ^ 2 * mu4) := by
    rw [hC6]
    ring
  have hsigma6pos : 0 < sigma ^ 6 := by
    positivity
  have hmu3sq_nonneg : 0 <= mu3 ^ 2 := by
    positivity
  constructor
  · have hlower_pos : 0 < 7 * sigma ^ 6 + 2 * mu3 ^ 2 := by
      nlinarith
    nlinarith
  · nlinarith

end Omega.Conclusion
