import Omega.Combinatorics.FibonacciCube

namespace Omega.POM

/-- Paper label: `prop:pom-fiber-decompose`. -/
theorem paper_pom_fiber_decompose (m : ℕ)
    (hrec : ∀ k, 6 ≤ k →
      Omega.X.maxFiberMultiplicity k =
        Omega.X.maxFiberMultiplicity (k - 2) + Omega.X.maxFiberMultiplicity (k - 4))
    (x : Omega.X m) :
    Omega.X.fiberMultiplicity x ≤ 2 * Nat.fib (m / 2 + 2) := by
  exact (Omega.X.fiberMultiplicity_le_max x).trans
    (Omega.maxFiberMultiplicity_le_two_mul_fib_half_of_two_step m hrec)

end Omega.POM
