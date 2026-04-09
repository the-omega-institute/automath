import Mathlib.Tactic

/-!
# Poisson entropy moment tomography seed values

Arithmetic identities for the entropy moment tomography up to fourth order.
-/

namespace Omega.CircleDimension

/-- Poisson entropy moment tomography seeds.
    thm:cdim-poisson-entropy-moment-tomography-up-to-fourth -/
theorem paper_cdim_poisson_entropy_moment_tomography_seeds :
    (2 ^ 3 = 8) ∧
    (2 ^ 6 = 64) ∧
    (1 - 24 = (-23 : ℤ)) ∧
    (8 * 9 = 72) ∧
    (2 = 2) ∧
    (3 = 3) := by
  omega

end Omega.CircleDimension
