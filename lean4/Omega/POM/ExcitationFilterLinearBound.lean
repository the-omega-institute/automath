import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-excitation-filter-linear-bound`. Once the surviving-eigenvalue lower
bound and the RH square-root upper bound have been combined into the logarithmic inequality
`(b/2) log ρ ≤ k_b log(ρ/η)`, the linear excitation threshold and the RH-sharp specialization are
immediate. -/
theorem paper_pom_excitation_filter_linear_bound
    (ρ η : ℝ) (b k_b : ℕ)
    (hρ : 1 < ρ) (hη_pos : 0 < η) (hη_ltρ : η < ρ)
    (hlog_bound : ((b : ℝ) / 2) * Real.log ρ ≤ (k_b : ℝ) * Real.log (ρ / η)) :
    ((b : ℝ) / 2) * Real.log ρ / Real.log (ρ / η) ≤ k_b ∧
      (η = Real.sqrt ρ → (b : ℝ) ≤ k_b) := by
  have hρ_pos : 0 < ρ := lt_trans zero_lt_one hρ
  have hη_inv_pos : 0 < η⁻¹ := inv_pos.mpr hη_pos
  have hratio_gt_one : 1 < ρ / η := by
    have hscaled : η * η⁻¹ < ρ * η⁻¹ := mul_lt_mul_of_pos_right hη_ltρ hη_inv_pos
    simpa [div_eq_mul_inv, hη_pos.ne'] using hscaled
  have hlog_ratio_pos : 0 < Real.log (ρ / η) := Real.log_pos hratio_gt_one
  constructor
  · rw [div_le_iff₀ hlog_ratio_pos]
    exact hlog_bound
  · intro hη_eq
    have hsqrt_pos : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ_pos
    have hratio_eq : Real.log (ρ / η) = (1 / 2 : ℝ) * Real.log ρ := by
      rw [hη_eq, Real.log_div (ne_of_gt hρ_pos) (ne_of_gt hsqrt_pos), Real.log_sqrt hρ_pos.le]
      ring
    have hlogρ_pos : 0 < Real.log ρ := Real.log_pos hρ
    rw [hratio_eq] at hlog_bound
    have hsharp : (b : ℝ) * Real.log ρ ≤ (k_b : ℝ) * Real.log ρ := by
      nlinarith
    have hk : (b : ℝ) ≤ k_b := by
      by_contra hlt
      have hlt' : (k_b : ℝ) < b := lt_of_not_ge hlt
      have hmul_lt : (k_b : ℝ) * Real.log ρ < (b : ℝ) * Real.log ρ :=
        mul_lt_mul_of_pos_right hlt' hlogρ_pos
      linarith
    exact hk

end Omega.POM
