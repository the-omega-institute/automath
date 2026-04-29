import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-bulk-curvature-bit-complexity-lower-bound`. -/
theorem paper_xi_bulk_curvature_bit_complexity_lower_bound {B : ℕ} {Δ amp : ℝ}
    (hΔ : 0 < Δ) (hAmpLower : Real.exp (Real.pi / Δ) ≤ amp)
    (hStable : amp ≤ 2 ^ (B : ℝ)) :
    Real.pi / (Real.log 2 * Δ) ≤ B := by
  have hExpToBits : Real.exp (Real.pi / Δ) ≤ (2 : ℝ) ^ (B : ℝ) :=
    le_trans hAmpLower hStable
  have hLogLe :
      Real.log (Real.exp (Real.pi / Δ)) ≤ Real.log ((2 : ℝ) ^ (B : ℝ)) :=
    Real.log_le_log (Real.exp_pos _) hExpToBits
  have hPiLe : Real.pi / Δ ≤ (B : ℝ) * Real.log 2 := by
    simpa [Real.log_rpow (by norm_num : (0 : ℝ) < 2), mul_comm] using hLogLe
  have hLog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDiv : (Real.pi / Δ) / Real.log 2 ≤ B :=
    (div_le_iff₀ hLog2).2 (by simpa [mul_comm] using hPiLe)
  calc
    Real.pi / (Real.log 2 * Δ) = (Real.pi / Δ) / Real.log 2 := by
      field_simp [hLog2.ne', hΔ.ne']
    _ ≤ B := hDiv

end Omega.Zeta
