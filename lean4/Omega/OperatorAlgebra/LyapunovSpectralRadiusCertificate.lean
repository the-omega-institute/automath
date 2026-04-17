import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Scalar Lyapunov witness for the strict spectral-radius bound in dimension one. -/
def scalarLyapunovWitness (a r H : ℝ) : Prop :=
  0 < H ∧ a ^ 2 * H < r ^ 2 * H

set_option maxHeartbeats 400000 in
/-- In dimension one, the strict spectral-radius bound is equivalent to the existence of a
positive Lyapunov certificate.
    prop:lyapunov-spectral-radius-certificate -/
theorem paper_op_algebra_lyapunov_spectral_radius_certificate (a r : ℝ) (hr : 0 < r) :
    |a| < r ↔ ∃ H : ℝ, scalarLyapunovWitness a r H := by
  constructor
  · intro ha
    refine ⟨1, ?_⟩
    constructor
    · norm_num
    · have hsq : a ^ 2 < r ^ 2 := by
        have hsqabs : |a| ^ 2 < r ^ 2 := by
          nlinarith [abs_nonneg a, ha, hr]
        simpa [sq_abs] using hsqabs
      simpa using hsq
  · rintro ⟨H, hH, hineq⟩
    have hsq : a ^ 2 < r ^ 2 := by
      nlinarith
    have hsqabs : |a| ^ 2 < r ^ 2 := by
      simpa [sq_abs] using hsq
    nlinarith [abs_nonneg a, hsqabs, hr]

end Omega.OperatorAlgebra
