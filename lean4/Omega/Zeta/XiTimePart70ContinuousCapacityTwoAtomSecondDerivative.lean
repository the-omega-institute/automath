import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.Ring

namespace Omega.Zeta

/-- The two slope jumps in the continuous two-atom capacity profile. -/
theorem paper_xi_time_part70_continuous_capacity_two_atom_second_derivative :
    ((Real.goldenRatio ^ 2 / Real.sqrt 5 - Real.goldenRatio / Real.sqrt 5 = 1 / Real.sqrt 5) ∧
      (Real.goldenRatio / Real.sqrt 5 - 0 = Real.goldenRatio / Real.sqrt 5)) := by
  constructor
  · rw [Real.goldenRatio_sq]
    ring
  · ring

end Omega.Zeta
