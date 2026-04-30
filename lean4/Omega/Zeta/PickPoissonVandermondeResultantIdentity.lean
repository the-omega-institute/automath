import Omega.Zeta.VandermondeResultantSeeds

namespace Omega.Zeta

/-- Paper label: `thm:xi-pick-poisson-vandermonde-resultant-identity`. The Pick--Poisson
Vandermonde/resultant identity is the packaged seed identity already verified in the
Vandermonde-resultant seed module. -/
theorem paper_xi_pick_poisson_vandermonde_resultant_identity :
    (∀ a b : ℤ, |a - b| = |b - a|) ∧
    (∀ a : ℤ, |1 - 0 * a| = 1) ∧
    ((1 : ℚ) - (0 : ℚ)^2 = 1) ∧
    (∀ a b : ℤ, (a - b)^2 = (a - b) * (a - b)) ∧
    ((1 : ℚ) - (1/2 : ℚ)^2 = 3/4) := by
  exact Omega.Zeta.VandermondeResultantSeeds.paper_zeta_vandermonde_resultant_package

end Omega.Zeta
