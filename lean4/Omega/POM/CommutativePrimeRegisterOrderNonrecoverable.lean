import Mathlib.Tactic
import Mathlib.Algebra.FreeMonoid.Basic

namespace Omega.POM.CommutativePrimeRegisterOrderNonrecoverable

open FreeMonoid

variable {α M : Type*} [CommMonoid M]

/-- Witness pair: for `a ≠ b`, the words `[a,b]` and `[b,a]` collapse under any
    commutative hom but are not equal in the free monoid.
    thm:pom-commutative-prime-register-order-nonrecoverable -/
theorem witness_pair_of_ne (Φ : FreeMonoid α →* M) (a b : α) (hab : a ≠ b) :
    Φ (of a * of b) = Φ (of b * of a) ∧
      (of a * of b : FreeMonoid α) ≠ of b * of a := by
  refine ⟨?_, ?_⟩
  · rw [Φ.map_mul, Φ.map_mul, mul_comm]
  · intro h
    have hlist : FreeMonoid.toList (of a * of b : FreeMonoid α) =
        FreeMonoid.toList (of b * of a : FreeMonoid α) := by
      rw [h]
    rw [FreeMonoid.toList_mul, FreeMonoid.toList_mul] at hlist
    -- toList (of a) = [a], toList (of b) = [b]
    change ([a] ++ [b] : List α) = [b] ++ [a] at hlist
    simp [List.cons.injEq] at hlist
    exact hab hlist.1

/-- Paper package: commutative prime register is not order-recoverable.
    thm:pom-commutative-prime-register-order-nonrecoverable -/
theorem paper_pom_commutative_prime_register_order_nonrecoverable
    (Φ : FreeMonoid α →* M) (a b : α) (hab : a ≠ b) :
    ¬ Function.Injective Φ := by
  intro hΦ_inj
  obtain ⟨h_eq, h_ne⟩ := witness_pair_of_ne Φ a b hab
  exact h_ne (hΦ_inj h_eq)

end Omega.POM.CommutativePrimeRegisterOrderNonrecoverable
