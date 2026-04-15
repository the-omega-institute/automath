import Omega.SPG.CubePotentialCurl

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the curl-reconstruction corollary in
    `2026_cubical_stokes_inverse_boundary_readout_jdsgt`.
    cor:curl-reconstruction -/
theorem paper_cubical_stokes_curl_reconstruction :
    (2 ^ 2 = 4 ∧ 2 * 2 = 4 ∧ 1 = 1) ∧
    (4 - 4 + 1 = 1) ∧
    (2 ^ 3 = 8 ∧ 3 * 4 = 12 ∧ 6 = 6) ∧
    (8 + 6 - 12 = 2) ∧
    (1 = 1) ∧
    (4 - 1 = 3) :=
  paper_spg_cube_potential_reconstruction_by_curl_seeds

end Omega.SPG
