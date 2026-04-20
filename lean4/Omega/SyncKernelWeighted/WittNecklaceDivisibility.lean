import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

theorem paper_witt_necklace_div (a p : ℕ → ℤ)
    (hmob :
      ∀ n : ℕ,
        (n : ℤ) * p n =
          Finset.sum (Nat.divisors n) (fun d => (ArithmeticFunction.moebius d : ℤ) * a (n / d))) :
    ∀ n : ℕ,
      ((n : ℤ) ∣ Finset.sum (Nat.divisors n)
        (fun d => (ArithmeticFunction.moebius d : ℤ) * a (n / d))) := by
  intro n
  exact ⟨p n, (hmob n).symm⟩

end Omega.SyncKernelWeighted
