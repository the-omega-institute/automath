import Omega.Folding.FibonacciPolynomial

namespace Omega

/-- Paper label: `prop:pom-fib-cassini-unified`. -/
theorem paper_pom_fib_cassini_unified (n : Nat) :
    (Nat.fib n : Int) * Nat.fib (n + 2) =
      (Nat.fib (n + 1) : Int) ^ 2 + (-1 : Int) ^ (n + 1) := by
  exact fib_product_cassini n

end Omega
