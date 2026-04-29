import Omega.SPG.PolycubeAdhesion

namespace Omega.SPG

/-- Paper label: `thm:spg-polyclube-adhesion-sharp-upper-bound`.
This file re-exports the existing arithmetic seed for the sharp adhesion bound under the paper's
historical `polyclube` spelling. -/
theorem paper_spg_polyclube_adhesion_sharp_upper_bound :
    (2 * 1 * 1 - 2 * 0 = (2 : ℤ)) ∧
    (2 * 1 * 2 - 2 * 1 = (2 : ℤ)) ∧
    (2 * 2 * 1 - 2 * 0 = (4 : ℤ)) ∧
    (2 * 2 * 4 - 2 * 4 = (8 : ℤ)) ∧
    (0 ≤ 1 * 1 * (2 - 1) / 2) ∧
    (1 ≤ 1 * 2 * (2 - 1) / 2) ∧
    (4 ≤ 2 * 4 * (2 - 1) / 2) ∧
    (2 * 4 ≤ 2 * 2 * (4 - 1)) := by
  exact Omega.SPG.PolycubeAdhesion.paper_spg_polycube_adhesion_sharp_upper_bound

end Omega.SPG
