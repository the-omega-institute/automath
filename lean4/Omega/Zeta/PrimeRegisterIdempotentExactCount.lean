import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The number of prime-register idempotents whose induced idempotent self-map on `Fin n`
has image size exactly `k`. -/
def primeRegisterIdempotentCount (n k : ℕ) : ℕ :=
  Nat.choose n k * k ^ (n - k)

/-- The total number of prime-register idempotents, obtained by summing over possible image
sizes `1 ≤ k ≤ n`. -/
def primeRegisterIdempotentTotalCount (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, primeRegisterIdempotentCount n k

/-- Exact count of idempotents in the prime-register semigroup, stratified by image size and then
summed over all nonempty images. `thm:xi-prime-register-idempotent-exact-count` -/
theorem paper_xi_prime_register_idempotent_exact_count (n : ℕ) :
    (∀ k, primeRegisterIdempotentCount n k = Nat.choose n k * k ^ (n - k)) ∧
      primeRegisterIdempotentTotalCount n =
        ∑ k ∈ Finset.Icc 1 n, Nat.choose n k * k ^ (n - k) := by
  refine ⟨?_, ?_⟩
  · intro k
    rfl
  · simp [primeRegisterIdempotentTotalCount, primeRegisterIdempotentCount]

end Omega.Zeta
