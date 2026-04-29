import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

open Filter Topology

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-frozen-first-difference-recovers-maxfiber-exponent`.

This concrete wrapper isolates the algebraic core of the frozen first-difference
argument: after the common `K_m` term has cancelled, the normalized log quotient
is exactly the normalized log maximal-fiber scale, and the pressure difference is
the same exponent. -/
def conclusion_frozen_first_difference_recovers_maxfiber_exponent_statement : Prop :=
  ∀ (a : ℤ) (alpha_star : ℝ) (S : ℤ → ℕ → ℝ) (M : ℕ → ℝ) (P : ℤ → ℝ),
    (∀ m : ℕ, S a m / S (a - 1) m = M m) →
      Tendsto (fun m : ℕ => Real.log (M m) / (m : ℝ)) atTop (𝓝 alpha_star) →
        P a = P (a - 1) + alpha_star →
          Tendsto (fun m : ℕ => Real.log (S a m / S (a - 1) m) / (m : ℝ)) atTop
              (𝓝 alpha_star) ∧
            P a - P (a - 1) = alpha_star

/-- Paper label:
`thm:conclusion-frozen-first-difference-recovers-maxfiber-exponent`. -/
theorem paper_conclusion_frozen_first_difference_recovers_maxfiber_exponent :
    conclusion_frozen_first_difference_recovers_maxfiber_exponent_statement := by
  intro a alpha_star S M P hquot hM hP
  constructor
  · convert hM using 1
    ext m
    rw [hquot m]
  · rw [hP]
    ring

end Omega.Conclusion
