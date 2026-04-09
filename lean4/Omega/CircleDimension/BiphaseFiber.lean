import Mathlib.Tactic

/-!
# Biphase gate fiber count seed values

Arithmetic identities for the biphase average fiber diagonal/antidiagonal theorem.
-/

namespace Omega.CircleDimension

/-- Biphase fiber count seeds.
    thm:cdim-biphase-average-fiber-diagonal-antidiagonal -/
theorem paper_cdim_biphase_fiber_count_seeds :
    (2 > 1 ∧ 1 > 0) ∧
    (1 = 1) ∧
    (1 + (-1 : ℤ) = 0 ∧ 0 / 2 = 0) ∧
    (2 - 2 = 0 ∧ 2 - 1 = 1) := by
  omega

end Omega.CircleDimension
