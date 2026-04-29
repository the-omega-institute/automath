import Omega.POM.ReplicaSoftcoreFibonacciPowerMomentCollapse

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite weighted moment statement for the replica-softcore Fibonacci collapse.  The
left-hand side is the binomial weighted geometric moment, and the prefactor clears the displayed
`2^{-m}` denominator from the paper statement. -/
def xi_replica_softcore_fibonacci_moment_collapse_statement (q m : ℕ) : Prop :=
  (2 : ℝ) ^ m * (∑ i : Fin (q + 1),
      ((Nat.choose q i.1 : ℝ) * (1 + 2 / Real.sqrt 5) ^ (q - i.1) *
        (1 - 2 / Real.sqrt 5) ^ i.1) *
        (((1 / 2 : ℝ) * Real.goldenRatio ^ (q - i.1) *
          Real.goldenConj ^ i.1) ^ m)) = (Nat.fib (m + 3) : ℝ) ^ q

/-- Paper label: `thm:xi-replica-softcore-fibonacci-moment-collapse`. -/
theorem paper_xi_replica_softcore_fibonacci_moment_collapse (q m : ℕ) :
    xi_replica_softcore_fibonacci_moment_collapse_statement q m := by
  exact Omega.POM.paper_pom_replica_softcore_fibonacci_power_moment_collapse q m

end

end Omega.Zeta
