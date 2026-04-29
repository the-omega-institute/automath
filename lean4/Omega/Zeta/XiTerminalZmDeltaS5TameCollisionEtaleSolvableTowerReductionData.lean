import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`cor:xi-terminal-zm-delta-s5-tame-collision-etale-solvable-tower-reduction-data`. -/
theorem paper_xi_terminal_zm_delta_s5_tame_collision_etale_solvable_tower_reduction_data :
    (60 / 12 = 5 ∧ 60 / 4 = 15 ∧ 60 / 2 = 30) ∧
      (10 - 5 = 5 ∧ 28 - 15 = 13 ∧ 55 - 30 = 25) ∧
        (60 - 30 = 30 ∧ 54 - 30 = 24) := by
  norm_num

end Omega.Zeta
