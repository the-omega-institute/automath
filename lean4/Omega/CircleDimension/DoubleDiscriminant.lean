import Mathlib.Tactic

/-!
# Double discriminant two-parameter family seed values

Power and factorial identities for the double discriminant synchronization family.
-/

namespace Omega.CircleDimension

/-- Double discriminant two-parameter seeds.
    prop:cdim-double-discriminant-two-parameter-family -/
theorem paper_cdim_double_discriminant_two_parameter_seeds :
    (2 = 2) ∧
    (256 = 4 ^ 4 ∧ 4 * 4 * 4 * 4 = 256) ∧
    (2 - 1 = 1) ∧
    (4 * 3 * 2 * 1 = 24) ∧
    (3 - 1 = 2) := by
  omega

end Omega.CircleDimension
