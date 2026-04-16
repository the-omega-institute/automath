import Omega.CircleDimension.CircleDim

namespace Omega.CircleDimension

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for the basic circle-dimension computation:
    the circle dimension is the free rank, finite torsion contributes zero,
    and the half-circle dimension of `ℕ^d` is `d / 2`.
    prop:circle-dimension-basic -/
theorem paper_cdim_basic_computation_seeds :
    (∀ r t : Nat, circleDim r t = r) ∧
      (∀ t : Nat, circleDim 0 t = 0) ∧
      (∀ r : Nat, circleDim r 0 = r) ∧
      (∀ d : Nat, halfCircleDim d 0 = (d : ℚ) / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r t
    simp [circleDim]
  · intro t
    simp [circleDim]
  · intro r
    simp [circleDim]
  · intro d
    simp [circleDim, halfCircleDim]

end Omega.CircleDimension
