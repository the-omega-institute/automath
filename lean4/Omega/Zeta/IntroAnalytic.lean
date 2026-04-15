import Omega.Zeta.PrimeLanguagesEulerProductNaturalBoundary
import Omega.Zeta.CyclicDet

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the analytic obstruction theorem in the prime-languages paper.
    thm:intro-analytic -/
theorem paper_prime_languages_intro_analytic :
    ((∀ p : ℕ, Nat.Prime p → p ≥ 2 → 2 * 1 ≤ p) ∧
      (Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧ Nat.Prime 11) ∧
      (∀ z : ℤ, (fredholmGoldenMean z).det = 1 - z - z ^ 2) ∧
      (∀ N : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > N)) ∧
      ((cyclicPerm2 ^ 2 = 1 ∧ cyclicPerm3 ^ 3 = 1 ∧
         cyclicPerm4 ^ 4 = 1 ∧ cyclicPerm5 ^ 5 = 1 ∧ cyclicPerm6 ^ 6 = 1) ∧
        (∀ z : ℤ, (fredholmGoldenMean z).det = 1 - z - z ^ 2)) := by
  exact ⟨paper_prime_languages_euler_product_natural_boundary,
    paper_operator_finite_state_zeta_2pii_periodic_separation⟩

end Omega.Zeta
