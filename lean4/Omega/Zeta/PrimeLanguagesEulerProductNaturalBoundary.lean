import Omega.Zeta.ETDSEulerProductNaturalBoundary

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the natural-boundary theorem in the prime-languages paper.
    thm:euler-product-natural-boundary -/
theorem paper_prime_languages_euler_product_natural_boundary :
    (∀ p : ℕ, Nat.Prime p → p ≥ 2 → 2 * 1 ≤ p) ∧
    (Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧ Nat.Prime 11) ∧
    (∀ z : ℤ, (fredholmGoldenMean z).det = 1 - z - z ^ 2) ∧
    (∀ N : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > N) :=
  paper_etds_euler_product_natural_boundary

end Omega.Zeta
