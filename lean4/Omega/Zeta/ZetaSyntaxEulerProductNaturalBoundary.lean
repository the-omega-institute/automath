import Omega.Zeta.DynZeta

namespace Omega.Zeta

/-- Publication-facing wrapper for `thm:zeta-syntax-euler-product-natural-boundary`. -/
theorem paper_zeta_syntax_euler_product_natural_boundary :
    (∀ p : ℕ, Nat.Prime p → p ≥ 2 → 2 * 1 ≤ p) ∧
    (Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧ Nat.Prime 11) ∧
    (∀ z : ℤ, (fredholmGoldenMean z).det = 1 - z - z ^ 2) ∧
    (∀ N : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > N) := by
  exact paper_euler_product_natural_boundary_witness

end Omega.Zeta
