import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Omega.Zeta.OffcriticalQuadraticRadialCompression
import Omega.Zeta.XiOffsetNullTypeSafety

namespace Omega.Zeta

/-- The dyadic visibility budget must dominate the off-critical boundary depth, and off-slice
points remain `NULL` in the unitary-slice semantics.
    cor:xi-offcritical-visibility-threshold-bit-budget -/
theorem paper_xi_offcritical_visibility_threshold_bit_budget
    {γ δ ρ b L : ℝ} {s : ℂ}
    (hδ : 0 < δ)
    (hdyad : 1 - ρ = (2 : ℝ) ^ (-b))
    (hvis : 1 - ρ ≤ appOffcriticalBoundaryDepth γ δ)
    (hL : 1 < L) (hs : s.re ≠ 1 / 2) :
    Real.log ((γ ^ 2 + (1 + δ) ^ 2) / (4 * δ)) ≤ b * Real.log 2 ∧
      xiOffsetPwClosureNull L s := by
  have hdepth :
      appOffcriticalBoundaryDepth γ δ = 4 * δ / (γ ^ 2 + (1 + δ) ^ 2) := by
    calc
      appOffcriticalBoundaryDepth γ δ = 4 * δ / (γ ^ 2 + (δ + 1) ^ 2) := by
        simpa using (paper_xi_offcritical_quadratic_radial_compression γ δ hδ).1.2.2
      _ = 4 * δ / (γ ^ 2 + (1 + δ) ^ 2) := by ring_nf
  have hres : (2 : ℝ) ^ (-b) ≤ 4 * δ / (γ ^ 2 + (1 + δ) ^ 2) := by
    simpa [hdyad, hdepth] using hvis
  have hpow_pos : 0 < (2 : ℝ) ^ (-b) := Real.rpow_pos_of_pos (by norm_num) _
  have hratio_pos : 0 < 4 * δ / (γ ^ 2 + (1 + δ) ^ 2) := by positivity
  have hlog :
      Real.log ((2 : ℝ) ^ (-b)) ≤ Real.log (4 * δ / (γ ^ 2 + (1 + δ) ^ 2)) :=
    Real.log_le_log hpow_pos hres
  have hpow_log : Real.log ((2 : ℝ) ^ (-b)) = -b * Real.log 2 := by
    rw [Real.log_rpow (show 0 < (2 : ℝ) by norm_num)]
  have h4δ_ne : 4 * δ ≠ 0 := by positivity
  have hden_ne : γ ^ 2 + (1 + δ) ^ 2 ≠ 0 := by positivity
  have hratio_inv :
      (γ ^ 2 + (1 + δ) ^ 2) / (4 * δ) = (4 * δ / (γ ^ 2 + (1 + δ) ^ 2))⁻¹ := by
    field_simp [h4δ_ne, hden_ne]
  have hbudget :
      Real.log ((γ ^ 2 + (1 + δ) ^ 2) / (4 * δ)) ≤ b * Real.log 2 := by
    rw [hratio_inv, Real.log_inv]
    rw [hpow_log] at hlog
    linarith
  exact ⟨hbudget, (paper_xi_offset_null_type_safety hL hs).2.2⟩

end Omega.Zeta
