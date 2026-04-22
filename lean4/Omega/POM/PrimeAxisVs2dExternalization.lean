import Mathlib.Tactic
import Omega.POM.CommutativePrimeRegisterOrderNonrecoverable
import Omega.POM.PrimeDeterminant2x2FreeEncoding

namespace Omega.POM.PrimeAxisVs2dExternalization

/-- No injective monoid hom from `FreeMonoid α` to a commutative monoid (part 1).
    thm:pom-prime-axis-vs-2d-noncommutative-externalization -/
theorem paper_pom_prime_axis_vs_2d_noncommutative_externalization_part1
    {α M : Type*} [CommMonoid M]
    (Φ : FreeMonoid α →* M) (a b : α) (hab : a ≠ b) :
    ¬ Function.Injective Φ :=
  CommutativePrimeRegisterOrderNonrecoverable.paper_pom_commutative_prime_register_order_nonrecoverable Φ a b hab

/-- Exchange between commutative prime-axis externalization failure and the
explicit `2 × 2` noncommutative free encoding. -/
theorem paper_pom_prime_axis_vs_2d_noncommutative_externalization
    {M : Type*} [CommMonoid M] {k N : ℕ} (Φ : FreeMonoid (Fin k) →* M) (p : Fin k → ℕ)
    (hk : 2 ≤ k) (hprime : ∀ i, Nat.Prime (p i)) (hN : 1 ≤ N) (hbound : ∀ i, p i < N) :
    ¬ Function.Injective Φ ∧ Function.Injective (primeDetWordMatrix N p) := by
  have hk0 : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  have hk1 : 1 < k := lt_of_lt_of_le (by decide : 1 < 2) hk
  let i0 : Fin k := ⟨0, hk0⟩
  let i1 : Fin k := ⟨1, hk1⟩
  have h01 : i0 ≠ i1 := by
    intro h
    have hzero_ne_one : (0 : ℕ) ≠ 1 := by decide
    apply hzero_ne_one
    simpa [i0, i1] using congrArg Fin.val h
  refine ⟨paper_pom_prime_axis_vs_2d_noncommutative_externalization_part1 Φ i0 i1 h01, ?_⟩
  exact (Omega.POM.paper_pom_prime_determinant_2x2_free_encoding p hprime hN hbound).2

end Omega.POM.PrimeAxisVs2dExternalization
