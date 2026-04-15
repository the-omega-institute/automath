import Mathlib.Tactic
import Omega.POM.CommutativePrimeRegisterOrderNonrecoverable

namespace Omega.POM.PrimeAxisVs2dExternalization

/-- No injective monoid hom from `FreeMonoid α` to a commutative monoid (part 1).
    thm:pom-prime-axis-vs-2d-noncommutative-externalization -/
theorem paper_pom_prime_axis_vs_2d_noncommutative_externalization_part1
    {α M : Type*} [CommMonoid M]
    (Φ : FreeMonoid α →* M) (a b : α) (hab : a ≠ b) :
    ¬ Function.Injective Φ :=
  CommutativePrimeRegisterOrderNonrecoverable.paper_pom_commutative_prime_register_order_nonrecoverable Φ a b hab

end Omega.POM.PrimeAxisVs2dExternalization
