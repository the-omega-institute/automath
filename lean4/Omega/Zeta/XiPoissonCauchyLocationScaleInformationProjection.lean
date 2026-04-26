import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-poisson-cauchy-location-scale-information-projection`. -/
theorem paper_xi_poisson_cauchy_location_scale_information_projection (A B : ℝ) :
    (∀ α β : ℝ,
      A ^ 2 / 16 + B ^ 2 / 4 ≤
        ((α - A / 2) ^ 2 + (β + B) ^ 2) + A ^ 2 / 16 + B ^ 2 / 4) ∧
      ((fun α β : ℝ =>
        ((α - A / 2) ^ 2 + (β + B) ^ 2) + A ^ 2 / 16 + B ^ 2 / 4)
          (A / 2) (-B) =
        A ^ 2 / 16 + B ^ 2 / 4) := by
  constructor
  · intro α β
    nlinarith [sq_nonneg (α - A / 2), sq_nonneg (β + B)]
  · ring

end Omega.Zeta
