import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zbc-foldpi-zeta-rank-jump`. -/
theorem paper_xi_time_part9zbc_foldpi_zeta_rank_jump
    {φ : ℝ} (hφ : φ ^ 2 = φ + 1) (hφ0 : φ ≠ 0) :
    (let g0 : ℝ := 2 / φ
     let g1 : ℝ := φ⁻¹ + φ
     let g2 : ℝ := φ⁻¹ + φ ^ 3
     g0 * g2 - g1 ^ 2 = 1) := by
  dsimp
  field_simp [hφ0]
  nlinarith [hφ]

end Omega.Zeta
