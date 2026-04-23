import Omega.Zeta.CyclicDet

namespace Omega.Zeta

/-- Paper label: `prop:cycle-permutation-determinant`. -/
theorem paper_cycle_permutation_determinant (t : ℤ) :
    (1 - t • cyclicPerm2).det = 1 - t ^ 2 ∧
      (1 - t • cyclicPerm3).det = 1 - t ^ 3 ∧
      (1 - t • cyclicPerm4).det = 1 - t ^ 4 ∧
      (1 - t • cyclicPerm5).det = 1 - t ^ 5 ∧
      (1 - t • cyclicPerm6).det = 1 - t ^ 6 := by
  exact ⟨cyclicPerm2_fredholm_det t, cyclicPerm3_fredholm_det t, cyclicPerm4_fredholm_det t,
    cyclicPerm5_fredholm_det t, cyclicPerm6_fredholm_det t⟩

end Omega.Zeta
