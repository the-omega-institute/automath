import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-terminal-zm-leyang-ply-root-chebyshev-cubic`. -/
theorem paper_xi_terminal_zm_leyang_ply_root_chebyshev_cubic {K : Type} [Field K]
    [CharZero K] (sqrt7 s : K) (h : s ^ 3 - 3 * s = -(1132 * sqrt7 / 49)) :
    49 * s ^ 3 - 147 * s + 1132 * sqrt7 = 0 := by
  have h49 : (49 : K) ≠ 0 := by norm_num
  have hmul : (49 : K) * (s ^ 3 - 3 * s) = -(1132 * sqrt7) := by
    calc
      (49 : K) * (s ^ 3 - 3 * s) = (49 : K) * (-(1132 * sqrt7 / 49)) := by
        rw [h]
      _ = -(1132 * sqrt7) := by
        field_simp [h49]
  linear_combination hmul

end Omega.Zeta
