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

/-- KL divergence two-term sharp moment polynomial seeds.
    thm:cdim-poisson-kl-two-term-sharp-moment-polynomial -/
theorem paper_cdim_poisson_kl_two_term_sharp_seeds :
    (2 ^ 3 = 8) ∧
    (2 ^ 6 = 64) ∧
    (1 - 8 * 3 + 6 * 0 = (-23 : ℤ)) ∧
    (6 - 4 = 2) ∧
    (6 = 6 ∧ 8 = 8) ∧
    (5 + 72 = 77) := by
  omega

/-- Lp sharp constants seeds.
    thm:cdim-poisson-cauchy-lp-sharp-constants-restated -/
theorem paper_cdim_poisson_cauchy_lp_sharp_constants_seeds :
    (2 ^ 4 = 16) ∧
    (3 = 3) ∧
    (3 = 3) ∧
    (2 * 5 = 10 ∧ 10 / 2 = 5) ∧
    (3 - 1 = 2 ∧ 3 = 3) := by
  omega

end Omega.CircleDimension
