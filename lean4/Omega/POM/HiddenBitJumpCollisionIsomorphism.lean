import Mathlib.Tactic
import Omega.Folding.CollisionDecomp

namespace Omega.POM

/-- Paper label: `thm:pom-hiddenbit-jump-collision-isomorphism`. The mixed hidden-bit collision
count is exactly the shifted cross-weight correlation, and the collision decomposition already
identifies this quantity with `S₂(m)`. -/
theorem paper_pom_hiddenbit_jump_collision_isomorphism (m : ℕ) :
    crossWeightCorrelation (m + 2) = momentSum 2 m ∧
      ∑ x : X (m + 2), fiberHiddenBitCount 0 x * fiberHiddenBitCount 1 x = momentSum 2 m := by
  constructor
  · exact crossWeightCorrelation_eq_momentSum_two m
  · rw [fiberHiddenBitCount_cross_eq_cwc, crossWeightCorrelation_eq_momentSum_two]

end Omega.POM
