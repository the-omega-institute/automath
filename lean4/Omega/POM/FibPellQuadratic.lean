import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.POM.FibPellQuadratic

open Nat

/-- Fibonacci Pell quadratic form (even): F_{2k+1}² = F_{2k}·F_{2k+1} + F_{2k}² + 1.
    Derived from Cassini even: F_{2k}·F_{2k+2} + 1 = F_{2k+1}² with F_{2k+2} = F_{2k+1} + F_{2k}.
    prop:pom-fib-pell-quadratic-characterization -/
theorem fib_pell_even (k : ℕ) :
    Nat.fib (2 * k + 1) ^ 2 =
      Nat.fib (2 * k) * Nat.fib (2 * k + 1) + Nat.fib (2 * k) ^ 2 + 1 := by
  have hcas := Omega.fib_cassini_even_indexed k
  -- hcas : F(2k+1)^2 = F(2k) * F(2k+2) + 1
  have hrec : Nat.fib (2 * k + 2) = Nat.fib (2 * k) + Nat.fib (2 * k + 1) := Nat.fib_add_two
  nlinarith [sq_nonneg (Nat.fib (2 * k))]

/-- Fibonacci Pell quadratic form (odd): F_{2k+2}² + 1 = F_{2k+1}·F_{2k+2} + F_{2k+1}².
    Derived from Cassini odd: F_{2k+1}·F_{2k+3} = F_{2k+2}² + 1 with F_{2k+3} = F_{2k+2} + F_{2k+1}.
    prop:pom-fib-pell-quadratic-characterization -/
theorem fib_pell_odd (k : ℕ) :
    Nat.fib (2 * k + 2) ^ 2 + 1 =
      Nat.fib (2 * k + 1) * Nat.fib (2 * k + 2) + Nat.fib (2 * k + 1) ^ 2 := by
  have hcas := Omega.fib_cassini_odd_indexed k
  -- hcas : F(2k+2)^2 + 1 = F(2k+1) * F(2k+3)
  have hrec : Nat.fib (2 * k + 3) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := Nat.fib_add_two
  nlinarith [sq_nonneg (Nat.fib (2 * k + 1))]

/-- Paper seeds: Pell quadratic at small indices.
    prop:pom-fib-pell-quadratic-characterization -/
theorem paper_pom_fib_pell_quadratic :
    Nat.fib 1 ^ 2 = Nat.fib 0 * Nat.fib 1 + Nat.fib 0 ^ 2 + 1 ∧
    Nat.fib 2 ^ 2 + 1 = Nat.fib 1 * Nat.fib 2 + Nat.fib 1 ^ 2 ∧
    Nat.fib 3 ^ 2 = Nat.fib 2 * Nat.fib 3 + Nat.fib 2 ^ 2 + 1 ∧
    Nat.fib 4 ^ 2 + 1 = Nat.fib 3 * Nat.fib 4 + Nat.fib 3 ^ 2 := by
  native_decide

end Omega.POM.FibPellQuadratic
