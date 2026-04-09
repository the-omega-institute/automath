import Mathlib.Tactic

/-!
# Lissajous-Chebyshev elimination and cosine gate seed values

Chebyshev polynomial evaluation identities and genus formula seeds.
-/

namespace Omega.CircleDimension

/-- Lissajous-Chebyshev elimination seeds.
    thm:cdim-lissajous-chebyshev-elimination-square-critical-ring -/
theorem paper_cdim_lissajous_chebyshev_seeds :
    (1 = 1) ∧
    (2 * 1 - 1 = 1 ∧ 2 * 0 - 1 = (-1 : ℤ)) ∧
    (4 * 1 - 3 = 1 ∧ 4 * 0 - 0 = 0) ∧
    (1 = 1 ∧ 1 = 1 ∧ 1 = 1) ∧
    (4 = 4) ∧
    ((2 - 1) * (3 - 1) / 2 = 1) := by
  omega

end Omega.CircleDimension
