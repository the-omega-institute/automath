import Omega.Combinatorics.FibonacciCube

namespace Omega.POM

/-- The single-coordinate marginal under the uniform measure on `Omega.X n`. -/
noncomputable def fibCubeMarginalProb (n : Nat) (i : Fin n) : Rat :=
  (Omega.coordOneCount n i : Rat) / (Fintype.card (Omega.X n) : Rat)

/-- Exact Fibonacci-cube one-site marginal. The asymptotic boundary-layer estimate can be derived
later from this closed form. `cor:pom-fibcube-marginal-boundary-layer` -/
theorem paper_pom_fibcube_marginal_boundary_layer (n : Nat) (i : Fin n) :
    fibCubeMarginalProb n i =
      ((Nat.fib (i.val + 1) * Nat.fib (n - i.val) : Nat) : Rat) / (Nat.fib (n + 2) : Rat) := by
  simp [fibCubeMarginalProb, Omega.coordOneCount_eq_fib_prod, Omega.X.card_eq_fib]

end Omega.POM
