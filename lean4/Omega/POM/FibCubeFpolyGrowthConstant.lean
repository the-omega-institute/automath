import Omega.Combinatorics.FibonacciCube

namespace Omega.POM

/-- Paper-facing package of the Fibonacci-cube growth recurrence and parity closed forms.
    cor:pom-fibcube-fpoly-growth-constant -/
theorem paper_pom_fibcube_fpoly_growth_constant (n : Nat) :
    totalFibcubeFVector (n + 2) =
        totalFibcubeFVector (n + 1) + 2 * totalFibcubeFVector n ∧
      (n % 2 = 0 → 3 * totalFibcubeFVector n + 1 = 2 ^ (n + 2)) ∧
      (n % 2 = 1 → 3 * totalFibcubeFVector n = 2 ^ (n + 2) + 1) := by
  refine ⟨Omega.totalFibcubeFVector_succ_succ n, ?_, ?_⟩
  · intro hn
    exact Omega.totalFibcubeFVector_closed_even n hn
  · intro hn
    exact Omega.totalFibcubeFVector_closed_odd n hn

end Omega.POM
