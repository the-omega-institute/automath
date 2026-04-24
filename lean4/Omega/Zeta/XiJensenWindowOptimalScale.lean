import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.Zeta.XiScaledShiftedJensenImpliesDeltaBound

namespace Omega.Zeta

/-- The quadratic coefficient `A(r) = (1 + r²) / (1 - r²)` from the scaled-shifted Jensen window
bound. -/
noncomputable def xi_jensen_window_optimal_scale_A (r : ℝ) : ℝ :=
  (1 + r ^ 2) / (1 - r ^ 2)

/-- The height half-window extracted from the concave quadratic certificate. -/
noncomputable def xi_jensen_window_optimal_scale_U (a r delta0 : ℝ) : ℝ :=
  Real.sqrt (max 0 (2 * a * xi_jensen_window_optimal_scale_A r * delta0 - a ^ 2 - delta0 ^ 2))

/-- Paper label: `thm:xi-jensen-window-optimal-scale`. Rewriting the admissible Jensen window as a
concave quadratic in the scale parameter shows that the half-width is maximized at the vertex
`a = δ₀ A(r)`, with maximal value `δ₀ * 2r / (1 - r²)`. -/
theorem paper_xi_jensen_window_optimal_scale
    {r delta0 : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hdelta0 : 0 < delta0) :
    let A := xi_jensen_window_optimal_scale_A r
    let U := xi_jensen_window_optimal_scale_U
    (∀ a : ℝ, 0 ≤ U a r delta0) ∧
      (∀ a : ℝ, (U a r delta0) ^ 2 = max 0 (2 * a * A * delta0 - a ^ 2 - delta0 ^ 2)) ∧
      (∀ a : ℝ, (U a r delta0) ^ 2 ≤ delta0 ^ 2 * (A ^ 2 - 1)) ∧
      U (delta0 * A) r delta0 = delta0 * (2 * r) / (1 - r ^ 2) ∧
      (∀ a : ℝ, U a r delta0 ≤ U (delta0 * A) r delta0) := by
  dsimp
  let A : ℝ := xi_jensen_window_optimal_scale_A r
  let U : ℝ → ℝ := fun a => xi_jensen_window_optimal_scale_U a r delta0
  have hden_pos : 0 < 1 - r ^ 2 := by
    nlinarith [sq_nonneg r, hr0, hr1]
  have hA_ge_one : 1 ≤ A := by
    unfold A xi_jensen_window_optimal_scale_A
    exact (le_div_iff₀ hden_pos).2 (by nlinarith [sq_nonneg r])
  have hpeak_nonneg : 0 ≤ delta0 ^ 2 * (A ^ 2 - 1) := by
    have hA_sq_ge_one : 1 ≤ A ^ 2 := by nlinarith [hA_ge_one]
    nlinarith [sq_nonneg delta0, hA_sq_ge_one]
  have hU_sq :
      ∀ a : ℝ, U a ^ 2 = max 0 (2 * a * A * delta0 - a ^ 2 - delta0 ^ 2) := by
    intro a
    unfold U xi_jensen_window_optimal_scale_U
    rw [Real.sq_sqrt]
    positivity
  have hupper_sq :
      ∀ a : ℝ, U a ^ 2 ≤ delta0 ^ 2 * (A ^ 2 - 1) := by
    intro a
    rw [hU_sq a]
    refine max_le_iff.mpr ?_
    constructor
    · exact hpeak_nonneg
    · nlinarith [sq_nonneg (a - delta0 * A)]
  have hopt_sq :
      U (delta0 * A) ^ 2 = (delta0 * (2 * r) / (1 - r ^ 2)) ^ 2 := by
    rw [hU_sq (delta0 * A)]
    have hinside :
        2 * (delta0 * A) * A * delta0 - (delta0 * A) ^ 2 - delta0 ^ 2 =
          delta0 ^ 2 * (A ^ 2 - 1) := by
      ring
    rw [hinside, max_eq_right hpeak_nonneg]
    unfold A xi_jensen_window_optimal_scale_A
    field_simp [hden_pos.ne']
    ring
  have hpeak_eq_rhs :
      delta0 ^ 2 * (A ^ 2 - 1) = (delta0 * (2 * r) / (1 - r ^ 2)) ^ 2 := by
    unfold A xi_jensen_window_optimal_scale_A
    field_simp [hden_pos.ne']
    ring
  have hopt :
      U (delta0 * A) = delta0 * (2 * r) / (1 - r ^ 2) := by
    have hU_nonneg : 0 ≤ U (delta0 * A) := by
      unfold U xi_jensen_window_optimal_scale_U
      positivity
    have hrhs_nonneg : 0 ≤ delta0 * (2 * r) / (1 - r ^ 2) := by
      positivity
    nlinarith [hopt_sq, hU_nonneg, hrhs_nonneg]
  have hmax :
      ∀ a : ℝ, U a ≤ U (delta0 * A) := by
    intro a
    have hUa_nonneg : 0 ≤ U a := by
      simpa [U, xi_jensen_window_optimal_scale_U] using
        (Real.sqrt_nonneg (max 0 (2 * a * A * delta0 - a ^ 2 - delta0 ^ 2)))
    have hUopt_nonneg : 0 ≤ U (delta0 * A) := by
      simpa [U, xi_jensen_window_optimal_scale_U] using
        (Real.sqrt_nonneg
          (max 0
            (2 * (delta0 * A) * A * delta0 - (delta0 * A) ^ 2 - delta0 ^ 2)))
    have hsq_le : U a ^ 2 ≤ U (delta0 * A) ^ 2 := by
      calc
        U a ^ 2 ≤ delta0 ^ 2 * (A ^ 2 - 1) := hupper_sq a
        _ = U (delta0 * A) ^ 2 := by rw [hopt_sq, hpeak_eq_rhs]
    nlinarith
  exact ⟨by
      intro a
      simpa [U, xi_jensen_window_optimal_scale_U] using
        (Real.sqrt_nonneg (max 0 (2 * a * A * delta0 - a ^ 2 - delta0 ^ 2))),
    hU_sq, hupper_sq, hopt, hmax⟩

end Omega.Zeta
