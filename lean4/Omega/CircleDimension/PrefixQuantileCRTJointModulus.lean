import Mathlib.Order.Lattice

namespace Omega.CircleDimension

/-- Paper-facing wrapper: combine the collision lower bound and the CRT tail budget by taking the
maximum of the two necessary modulus constraints.
cor:cdim-prefix-quantile-crt-joint-modulus -/
theorem paper_cdim_prefix_quantile_crt_joint_modulus
    (P collisionBound tailBound : Nat) (hCollision : collisionBound <= P)
    (hTail : 2 * tailBound <= P) : max collisionBound (2 * tailBound) <= P := by
  exact sup_le hCollision hTail

end Omega.CircleDimension
