import Omega.Combinatorics.FibonacciCube

namespace Omega.POM

/-- Paper-facing wrapper: the `i`-th Θ-class in the Fibonacci cube has size
    `F(i) * F(n-i+1)` after translating to zero-based `Fin` coordinates.
    thm:pom-fibcube-theta-class-size -/
theorem paper_pom_fibcube_theta_class_size (n : Nat) (i : Fin n) :
    Omega.coordOneCount n i = Nat.fib (i.val + 1) * Nat.fib (n - i.val) := by
  simpa using Omega.coordOneCount_eq_fib_prod n i

end Omega.POM
