import Omega.GU.LeyangHolographicN2

namespace Omega.GU

open Omega.GU.LeyangHolographicN2

variable {K : Type*} [Field K]

/-- The reciprocal quadratic factor attached to the roots `z₁`, `z₂`, evaluated at `u`.
    thm:group-jg-pullback-factorization -/
def quadraticReciprocalEval (u z₁ z₂ : K) : K := (1 - z₁ * u) * (1 - z₂ * u)

/-- Degree-2 pullback factorization for the Joukowsky-Gödel transport polynomial.
    thm:group-jg-pullback-factorization -/
theorem paper_group_jg_pullback_factorization
    (r z z₁ z₂ : K) (hr : r ≠ 0) (hz : z ≠ 0) :
    Q_r_eval_at_J r z z₁ z₂ * (r ^ 2 * z ^ 2) =
      P z z₁ z₂ * quadraticReciprocalEval (r ^ 2 * z) z₁ z₂ := by
  rw [paper_group_jg_leyang_holographic_identity_n2 r z z₁ z₂ hr hz]
  simp [P, quadraticReciprocalEval, mul_assoc, mul_left_comm, mul_comm]

end Omega.GU
