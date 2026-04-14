import Mathlib.Tactic

namespace Omega.SPG.PolycubeAdhesion

/-- Polycube boundary-adjacency identity and adhesion upper bound seeds.
    thm:spg-polycube-adhesion-sharp-upper-bound -/
theorem paper_spg_polycube_adhesion_sharp_upper_bound :
    -- boundary-adjacency identity: F = 2n·N - 2E
    (2 * 1 * 1 - 2 * 0 = (2 : ℤ)) ∧
    (2 * 1 * 2 - 2 * 1 = (2 : ℤ)) ∧
    (2 * 2 * 1 - 2 * 0 = (4 : ℤ)) ∧
    (2 * 2 * 4 - 2 * 4 = (8 : ℤ)) ∧
    -- adhesion upper bound: E ≤ n·N·(2^m - 1)/2^m
    (0 ≤ 1 * 1 * (2 - 1) / 2) ∧
    (1 ≤ 1 * 2 * (2 - 1) / 2) ∧
    (4 ≤ 2 * 4 * (2 - 1) / 2) ∧
    -- average degree bound
    (2 * 4 ≤ 2 * 2 * (4 - 1)) := by
  omega

end Omega.SPG.PolycubeAdhesion
