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

/-- Biphase average disk critical ring seeds.
    thm:cdim-biphase-average-disk-critical-ring -/
theorem paper_cdim_biphase_disk_critical_ring_seeds :
    (1 + 1 = 2 ∧ 2 / 2 = 1) ∧
    (1 = 1) ∧
    (1 - 1 = 0 ∧ 0 / 2 = 0) ∧
    (1 + 0 = 1 ∧ 2 - 1 = 1) ∧
    (1 + (-1 : ℤ) = 0 ∧ 1 + 1 = 2) := by
  omega

end Omega.CircleDimension
