import Omega.Combinatorics.FibonacciCube

namespace Omega.POM

/-- Paper-facing packaging of the Fibonacci-cube edge and vertex closed forms.
    cor:pom-fibcube-edge-closed-form -/
theorem paper_pom_fibcube_edge_closed_form (n : Nat) :
    Omega.fibcubeFVector n 1 = Omega.fibcubeEdgeCount n ∧
      5 * Omega.fibcubeEdgeCount n = n * Nat.fib (n + 1) + 2 * (n + 1) * Nat.fib n ∧
      Omega.fibcubeFVector n 0 = Nat.fib (n + 2) := by
  exact ⟨Omega.fibcubeFVector_one_eq_edge n, Omega.fibcubeEdgeCount_closed n,
    Omega.fibcubeFVector_zero_eq_fib n⟩

end Omega.POM
