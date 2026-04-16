import Omega.CircleDimension.GcdimPolynomialRing

namespace Omega.CircleDimension

/-- The arithmetic circle dimension attached to the polynomial-ring prime zeta package. -/
def polynomialRingArithmeticCircleDim (d : Nat) : Nat :=
  polynomialRingGrowthCircleDim d + 1

/-- Paper-facing statement: the polynomial ring in `d` variables has arithmetic circle dimension
    `d + 1`, i.e. one more than its growth circle dimension. -/
def paper_acdim_polynomial_ring_stmt (d : Nat) : Prop :=
  polynomialRingArithmeticCircleDim d = d + 1

theorem paper_acdim_polynomial_ring (d : Nat) : paper_acdim_polynomial_ring_stmt d := by
  unfold paper_acdim_polynomial_ring_stmt polynomialRingArithmeticCircleDim
  rw [paper_gcdim_polynomial_ring]

end Omega.CircleDimension
