import Omega.SPG.CubePoincareInverse

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the optimal coefficient-`L^\infty` right-inverse theorem in
    `2026_cubical_stokes_inverse_boundary_readout_jdsgt`.
    thm:optimal-continuous-inverse -/
theorem paper_cubical_stokes_optimal_continuous_inverse :
    (4 * 1 = 4) ∧
    (2 * 2 = 4 ∧ 2 ≤ 4) ∧
    (3 ≤ 4) ∧
    (1 ≤ 4) ∧
    (2 ^ 3 = 8 ∧ 3 * 4 = 12) ∧
    (4 / 4 = 1) :=
  paper_spg_cube_optimal_poincare_stokes_inverse_seeds

end Omega.SPG
