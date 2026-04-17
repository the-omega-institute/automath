import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The Bowen--Franks Fibonacci modulus attached to the `q`-th collision block. -/
def collisionAQFibonacciBFModulus (q : ℕ) : ℕ :=
  Nat.fib (2 * q - 2)

/-- A prime audit witness is fresh at level `q` if it divides the current even-index Fibonacci
modulus and does not divide any earlier even-index modulus. -/
def collisionAQFreshAuditPrime (q p : ℕ) : Prop :=
  Nat.Prime p ∧
    p ∣ collisionAQFibonacciBFModulus q ∧
    ∀ k : ℕ, 2 ≤ k → k < q → ¬ p ∣ collisionAQFibonacciBFModulus k

instance collisionAQFreshAuditPrimeDecidable (q p : ℕ) :
    Decidable (collisionAQFreshAuditPrime q p) := by
  unfold collisionAQFreshAuditPrime collisionAQFibonacciBFModulus
  infer_instance

/-- Concrete primitive-prime-divisor forcing seeds for the even-index Fibonacci BF moduli.  The
fresh audit primes `3, 2, 7, 11, 13` already appear at levels `q = 3, 4, 5, 6, 8`, so any audit
scheme covering these levels needs at least five distinct prime coordinates.
`prop:pom-collision-aq-fibonacci-bf-primitive-prime-divisor` -/
theorem paper_pom_collision_aq_fibonacci_bf_primitive_prime_divisor :
    collisionAQFreshAuditPrime 3 3 ∧
    collisionAQFreshAuditPrime 4 2 ∧
    collisionAQFreshAuditPrime 5 7 ∧
    collisionAQFreshAuditPrime 6 11 ∧
    collisionAQFreshAuditPrime 8 13 ∧
    ({2, 3, 7, 11, 13} : Finset ℕ).card = 5 := by
  native_decide

end Omega.POM
