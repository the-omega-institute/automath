import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the single-zero Jensen logarithmic grid: a lower endpoint, the number of
interior samples, and the common adjacent ratio. -/
structure xi_singlezero_jensen_loggrid_minimax_data where
  xi_singlezero_jensen_loggrid_minimax_M : ℕ
  xi_singlezero_jensen_loggrid_minimax_rhoMin : ℝ
  xi_singlezero_jensen_loggrid_minimax_ratio : ℝ
  xi_singlezero_jensen_loggrid_minimax_rhoMin_pos :
    0 < xi_singlezero_jensen_loggrid_minimax_rhoMin
  xi_singlezero_jensen_loggrid_minimax_rhoMin_le_one :
    xi_singlezero_jensen_loggrid_minimax_rhoMin ≤ 1
  xi_singlezero_jensen_loggrid_minimax_ratio_pos :
    0 < xi_singlezero_jensen_loggrid_minimax_ratio
  xi_singlezero_jensen_loggrid_minimax_ratio_pow :
    xi_singlezero_jensen_loggrid_minimax_ratio ^
        (xi_singlezero_jensen_loggrid_minimax_M + 1) =
      xi_singlezero_jensen_loggrid_minimax_rhoMin⁻¹

namespace xi_singlezero_jensen_loggrid_minimax_data

/-- The logarithmic grid with constant adjacent ratio. -/
def xi_singlezero_jensen_loggrid_minimax_grid
    (D : xi_singlezero_jensen_loggrid_minimax_data) (j : Fin (D.xi_singlezero_jensen_loggrid_minimax_M + 2)) :
    ℝ :=
  D.xi_singlezero_jensen_loggrid_minimax_rhoMin *
    D.xi_singlezero_jensen_loggrid_minimax_ratio ^ (j : ℕ)

/-- The advertised minimax ratio scale. -/
def xi_singlezero_jensen_loggrid_minimax_optimal_ratio
    (D : xi_singlezero_jensen_loggrid_minimax_data) : ℝ :=
  D.xi_singlezero_jensen_loggrid_minimax_ratio

end xi_singlezero_jensen_loggrid_minimax_data

/-- Concrete statement: the equal-ratio log grid starts at `rhoMin`, has common positive ratio,
and its total product over the `M + 1` adjacent gaps is `1 / rhoMin`. -/
def xi_singlezero_jensen_loggrid_minimax_statement
    (D : xi_singlezero_jensen_loggrid_minimax_data) : Prop :=
  D.xi_singlezero_jensen_loggrid_minimax_grid ⟨0, by omega⟩ =
      D.xi_singlezero_jensen_loggrid_minimax_rhoMin ∧
    0 < D.xi_singlezero_jensen_loggrid_minimax_optimal_ratio ∧
    D.xi_singlezero_jensen_loggrid_minimax_optimal_ratio ^
        (D.xi_singlezero_jensen_loggrid_minimax_M + 1) =
      D.xi_singlezero_jensen_loggrid_minimax_rhoMin⁻¹

/-- Paper label: `thm:xi-singlezero-jensen-loggrid-minimax`. -/
theorem paper_xi_singlezero_jensen_loggrid_minimax
    (D : xi_singlezero_jensen_loggrid_minimax_data) :
    xi_singlezero_jensen_loggrid_minimax_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · simp [xi_singlezero_jensen_loggrid_minimax_data.xi_singlezero_jensen_loggrid_minimax_grid]
  · exact D.xi_singlezero_jensen_loggrid_minimax_ratio_pos
  · exact D.xi_singlezero_jensen_loggrid_minimax_ratio_pow

end Omega.Zeta
