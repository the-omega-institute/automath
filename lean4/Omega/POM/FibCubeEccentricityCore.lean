import Omega.Combinatorics.FibonacciCube

namespace Omega.POM.FibCubeEccentricityCore

/-- Core eccentricity seed: a Fibonacci-cube vertex has at most half-density support.
    thm:pom-fibcube-eccentricity-closed-form -/
theorem paper_pom_fibcube_eccentricity_core_seeds {L : ℕ} (x : Omega.X L) :
    Omega.popcount x.1 ≤ (L + 1) / 2 := by
  simpa [Omega.popcount] using Omega.popcount_le_half x

/-- Package for the Fibonacci-cube eccentricity core bound.
    thm:pom-fibcube-eccentricity-closed-form -/
theorem paper_pom_fibcube_eccentricity_core_package {L : ℕ} (x : Omega.X L) :
    Omega.popcount x.1 ≤ (L + 1) / 2 :=
  paper_pom_fibcube_eccentricity_core_seeds x

end Omega.POM.FibCubeEccentricityCore
