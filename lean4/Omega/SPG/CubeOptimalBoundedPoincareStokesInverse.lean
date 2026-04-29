import Omega.SPG.CubePoincareInverse

namespace Omega.SPG

/-- Paper-facing wrapper statement for the cube Poincare-Stokes inverse package. -/
def spg_cube_optimal_bounded_poincare_stokes_inverse_statement (n k : Nat) : Prop :=
  cubeHomotopyIdentityModel n k ∧
    cubeLinftyBoundModel n k ∧
    cubeOptimalityWitnessModel k

/-- Paper label: `thm:spg-cube-optimal-bounded-poincare-stokes-inverse`. This wraps the existing
cube homotopy identity, sharp `L^∞` coefficient bound, and optimality witness under the exact
paper-facing theorem name. -/
theorem paper_spg_cube_optimal_bounded_poincare_stokes_inverse (n k : Nat) :
    spg_cube_optimal_bounded_poincare_stokes_inverse_statement n k := by
  exact paper_spg_cube_optimal_poincare_stokes_inverse n k

end Omega.SPG
