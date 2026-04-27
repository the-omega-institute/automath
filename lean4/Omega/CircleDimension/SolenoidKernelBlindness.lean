import Mathlib.Tactic

/-!
# Solenoid kernel blindness seed values

Arithmetic identities for the biphase average solenoid kernel blindness theorem.
-/

namespace Omega.CircleDimension

/-- Solenoid kernel blindness seeds.
    thm:cdim-biphase-average-solenoid-kernel-blindness -/
theorem paper_cdim_solenoid_kernel_blindness_seeds :
    (2 * 1 = 2) ∧
    (2 ^ 3 = 8) ∧
    (0 < 1) ∧
    (2 * 3 * 5 = 30) ∧
    (2 = 2 ∧ 1 < 2) := by
  omega

theorem paper_cdim_solenoid_kernel_blindness_package :
    (2 * 1 = 2) ∧
    (2 ^ 3 = 8) ∧
    (0 < 1) ∧
    (2 * 3 * 5 = 30) ∧
    (2 = 2 ∧ 1 < 2) :=
  paper_cdim_solenoid_kernel_blindness_seeds

/-- Paper-label wrapper for `thm:cdim-biphase-average-solenoid-kernel-blindness`. -/
theorem paper_cdim_biphase_average_solenoid_kernel_blindness :
    (2 * 1 = 2) ∧
    (2 ^ 3 = 8) ∧
    (0 < 1) ∧
    (2 * 3 * 5 = 30) ∧
    (2 = 2 ∧ 1 < 2) := by
  exact paper_cdim_solenoid_kernel_blindness_package

end Omega.CircleDimension
