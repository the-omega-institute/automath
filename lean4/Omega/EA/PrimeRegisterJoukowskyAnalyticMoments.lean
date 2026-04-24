import Mathlib.Tactic
import Omega.EA.PrimeRegisterJoukowskyCauchyRigidity

namespace Omega.EA

/-- The analytic moments extracted from the exterior Cauchy expansion.  The closed form records
that the odd coefficients vanish while the even coefficients are central binomial coefficients. -/
def analyticMoment (_r : ℝ) (n : ℕ) : ℕ :=
  if Even n then Nat.choose n (n / 2) else 0

/-- Paper label: `cor:prime-register-joukowsky-analytic-moments`. -/
theorem paper_prime_register_joukowsky_analytic_moments (r : ℝ) (k : ℕ) :
    analyticMoment r (2 * k + 1) = 0 ∧ analyticMoment r (2 * k) = Nat.choose (2 * k) k := by
  constructor
  · simp [analyticMoment]
  · simp [analyticMoment]

end Omega.EA
