import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-cauchy-poisson-fdiv-sixth-order-expansion`. -/
theorem paper_xi_cauchy_poisson_fdiv_sixth_order_expansion
    (f2 f3 sigmaSq mu3 mu4 : ℝ) :
    ((f2 / 2) * (sigmaSq ^ 2 / 4) = f2 * sigmaSq ^ 2 / 8) ∧
      ((f2 / 2) * (3 * mu3 ^ 2 / 16 - sigmaSq * mu4 / 4) +
          (f3 / 6) * (-(3 * sigmaSq ^ 3 / 32)) =
        f2 * (3 * mu3 ^ 2 / 32 - sigmaSq * mu4 / 8) - f3 * sigmaSq ^ 3 / 64) := by
  constructor <;> ring

end Omega.Zeta
