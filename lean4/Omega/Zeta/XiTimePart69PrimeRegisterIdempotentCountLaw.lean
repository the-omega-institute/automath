import Omega.Zeta.PrimeRegisterIdempotentExactCount

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part69-prime-register-idempotent-count-law`. -/
theorem paper_xi_time_part69_prime_register_idempotent_count_law (n : ℕ) :
    (∀ k, 1 ≤ k → k ≤ n →
        primeRegisterIdempotentCount n k = Nat.choose n k * k ^ (n - k)) ∧
      primeRegisterIdempotentTotalCount n =
        ∑ k ∈ Finset.Icc 1 n, Nat.choose n k * k ^ (n - k) := by
  have h := paper_xi_prime_register_idempotent_exact_count n
  exact ⟨fun k _ _ => h.1 k, h.2⟩

end Omega.Zeta
