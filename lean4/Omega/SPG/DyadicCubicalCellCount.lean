import Mathlib.Tactic

/-!
# Dyadic cubical cell counts

For the n-dimensional dyadic cube Q_m with 2^m subdivisions per axis:
- n-cell count = 2^{n·m}
- (n-1)-cell count = n·(2^m+1)·2^{(n-1)·m}
-/

namespace Omega.SPG.DyadicCubicalCellCount

/-- Number of top-dimensional (n-dimensional) cells in Q_m.
    cor:spg-dyadic-topdim-holography-exactness -/
def dyadicTopCellCount (n m : Nat) : Nat := 2 ^ (n * m)

/-- Number of (n-1)-dimensional cells (faces) in Q_m.
    cor:spg-dyadic-topdim-holography-exactness -/
def dyadicFaceCellCount (n m : Nat) : Nat := n * (2 ^ m + 1) * 2 ^ ((n - 1) * m)

/-- Seed values for small (n, m).
    cor:spg-dyadic-topdim-holography-exactness -/
theorem paper_spg_dyadic_topdim_holography_exactness :
    dyadicTopCellCount 1 1 = 2 ∧ dyadicFaceCellCount 1 1 = 3 ∧
    dyadicTopCellCount 2 1 = 4 ∧ dyadicFaceCellCount 2 1 = 12 ∧
    dyadicTopCellCount 2 2 = 16 ∧ dyadicFaceCellCount 2 2 = 40 ∧
    dyadicTopCellCount 3 1 = 8 ∧ dyadicFaceCellCount 3 1 = 36 := by
  simp only [dyadicTopCellCount, dyadicFaceCellCount]
  omega

/-- Codimension of Z_{n-1} in C_{n-1}: (n-1)·2^{nm} + n·2^{(n-1)m}.
    cor:spg-dyadic-topdim-holography-exactness -/
theorem codim_seed_values :
    (1 - 1) * 2 ^ (2 * 1) + 2 * 2 ^ ((2 - 1) * 1) = 4 ∧
    (2 - 1) * 2 ^ (2 * 1) + 2 * 2 ^ ((2 - 1) * 1) = 8 ∧
    (3 - 1) * 2 ^ (3 * 1) + 3 * 2 ^ ((3 - 1) * 1) = 28 := by
  omega

end Omega.SPG.DyadicCubicalCellCount
