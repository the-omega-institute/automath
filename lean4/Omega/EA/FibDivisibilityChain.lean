import Omega.Core.Fib

namespace Omega.EA.FibDivisibilityChain

/-- Paper-facing seed for the Fibonacci divisibility chain.
    lem:fib-divisibility-chain -/
theorem paper_fib_divisibility_chain_seeds (a b : ℕ) (h : a ∣ b) :
    Nat.fib a ∣ Nat.fib b :=
  Nat.fib_dvd a b h

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_fib_divisibility_chain_package (a b : ℕ) (h : a ∣ b) :
    Nat.fib a ∣ Nat.fib b :=
  paper_fib_divisibility_chain_seeds a b h

end Omega.EA.FibDivisibilityChain
