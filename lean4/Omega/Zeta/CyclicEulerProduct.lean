import Omega.Zeta.CyclicDet

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: the basic cyclic Fredholm blocks recover the Euler factors
    `(1 - β r^n)^{-1}` for `2 ≤ n ≤ 6`.
    cor:cyclic-euler-product -/
theorem paper_cyclic_euler_product_seeds (α r : ℤ) :
    (1 - (α * r) • cyclicPerm2).det = 1 - (α * r) ^ 2 ∧
      (1 - (α * r) • cyclicPerm3).det = 1 - (α * r) ^ 3 ∧
      (1 - (α * r) • cyclicPerm4).det = 1 - (α * r) ^ 4 ∧
      (1 - (α * r) • cyclicPerm5).det = 1 - (α * r) ^ 5 ∧
      (1 - (α * r) • cyclicPerm6).det = 1 - (α * r) ^ 6 := by
  exact ⟨euler_factor_n2 α r, euler_factor_n3 α r, euler_factor_n4 α r,
    euler_factor_n5 α r, euler_factor_n6 α r⟩

end Omega.Zeta
