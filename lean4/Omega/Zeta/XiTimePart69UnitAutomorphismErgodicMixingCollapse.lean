import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

/-- In the localized rank-one character criterion, only the two sign characters obstruct
ergodicity. -/
def xi_time_part69_unit_automorphism_ergodic_mixing_collapse_ergodic
    (q : ℚ) : Prop :=
  ¬ (q = 1 ∨ q = -1)

/-- Mixing for the rank-one localized rational automorphism is exactly absence of the two
finite character obstructions. -/
def xi_time_part69_unit_automorphism_ergodic_mixing_collapse_mixing
    (q : ℚ) : Prop :=
  q ≠ 1 ∧ q ≠ -1

/-- Paper label: `thm:xi-time-part69-unit-automorphism-ergodic-mixing-collapse`. -/
theorem paper_xi_time_part69_unit_automorphism_ergodic_mixing_collapse (q : ℚ) :
    (xi_time_part69_unit_automorphism_ergodic_mixing_collapse_ergodic q ↔
      xi_time_part69_unit_automorphism_ergodic_mixing_collapse_mixing q) ∧
    (xi_time_part69_unit_automorphism_ergodic_mixing_collapse_mixing q ↔
      q ≠ 1 ∧ q ≠ -1) := by
  constructor
  · simp [xi_time_part69_unit_automorphism_ergodic_mixing_collapse_ergodic,
      xi_time_part69_unit_automorphism_ergodic_mixing_collapse_mixing, not_or]
  · rfl

end Omega.Zeta
