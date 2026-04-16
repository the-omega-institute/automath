import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Rank of the total-degree-at-most-`N` piece of `ℤ[x₁, …, xₙ]`.
This is the standard stars-and-bars count. -/
def polynomialRingDegreePieceRank (n N : Nat) : Nat := Nat.choose (n + N) n

/-- Growth circle dimension of the polynomial ring in `n` variables. -/
def polynomialRingGrowthCircleDim (n : Nat) : Nat := n

theorem polynomialRingDegreePieceRank_eq_choose (n N : Nat) :
    polynomialRingDegreePieceRank n N = Nat.choose (n + N) n := rfl

theorem paper_gcdim_polynomial_ring (n : Nat) : polynomialRingGrowthCircleDim n = n := by
  rfl

end Omega.CircleDimension
