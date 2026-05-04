import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete toric-rank table for the three boundary ranks in the S4 isotypic period map. -/
structure xi_s4_isotypic_period_map_maximal_degeneration_data where
  xi_s4_isotypic_period_map_toric_rank : Fin 3 → ℕ
  xi_s4_isotypic_period_map_expected_rank : Fin 3 → ℕ
  xi_s4_isotypic_period_map_rank_transfer :
    ∀ i,
      xi_s4_isotypic_period_map_toric_rank i =
        xi_s4_isotypic_period_map_expected_rank i
  xi_s4_isotypic_period_map_expected_rank_table :
    xi_s4_isotypic_period_map_expected_rank 0 = 1 ∧
      xi_s4_isotypic_period_map_expected_rank 1 = 2 ∧
        xi_s4_isotypic_period_map_expected_rank 2 = 3

namespace xi_s4_isotypic_period_map_maximal_degeneration_data

/-- Boundary rank-one case of maximal degeneration. -/
def xi_s4_isotypic_period_map_boundary_r1
    (D : xi_s4_isotypic_period_map_maximal_degeneration_data) : Prop :=
  D.xi_s4_isotypic_period_map_toric_rank 0 = 1

/-- Boundary rank-two case of maximal degeneration. -/
def xi_s4_isotypic_period_map_boundary_r2
    (D : xi_s4_isotypic_period_map_maximal_degeneration_data) : Prop :=
  D.xi_s4_isotypic_period_map_toric_rank 1 = 2

/-- Boundary rank-three case of maximal degeneration. -/
def xi_s4_isotypic_period_map_boundary_r3
    (D : xi_s4_isotypic_period_map_maximal_degeneration_data) : Prop :=
  D.xi_s4_isotypic_period_map_toric_rank 2 = 3

end xi_s4_isotypic_period_map_maximal_degeneration_data

/-- Paper label: `prop:xi-s4-isotypic-period-map-maximal-degeneration`. -/
theorem paper_xi_s4_isotypic_period_map_maximal_degeneration
    (D : xi_s4_isotypic_period_map_maximal_degeneration_data) :
    D.xi_s4_isotypic_period_map_boundary_r1 ∧ D.xi_s4_isotypic_period_map_boundary_r2 ∧
      D.xi_s4_isotypic_period_map_boundary_r3 := by
  rcases D.xi_s4_isotypic_period_map_expected_rank_table with ⟨hr1, hr2, hr3⟩
  refine ⟨?_, ?_, ?_⟩
  · change D.xi_s4_isotypic_period_map_toric_rank 0 = 1
    rw [D.xi_s4_isotypic_period_map_rank_transfer 0, hr1]
  · change D.xi_s4_isotypic_period_map_toric_rank 1 = 2
    rw [D.xi_s4_isotypic_period_map_rank_transfer 1, hr2]
  · change D.xi_s4_isotypic_period_map_toric_rank 2 = 3
    rw [D.xi_s4_isotypic_period_map_rank_transfer 2, hr3]

end Omega.Zeta
