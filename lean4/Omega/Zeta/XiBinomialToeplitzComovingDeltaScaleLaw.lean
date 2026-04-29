import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiBinomialToeplitzScaleDepthExchange

namespace Omega.Zeta

noncomputable section

/-- Comoving Cayley coordinate. -/
def xi_binomial_toeplitz_comoving_delta_scale_law_w (δ : ℝ) : ℝ :=
  (1 - δ) / (1 + δ)

/-- Comoving logarithmic scale. -/
def xi_binomial_toeplitz_comoving_delta_scale_law_Lambda (δ : ℝ) : ℝ :=
  Real.log ((1 + δ) / (1 - δ))

/-- Comoving depth proxy at fixed scale budget `c`. -/
def xi_binomial_toeplitz_comoving_delta_scale_law_m (δ c : ℝ) : ℝ :=
  c / δ

/-- Paper label: `thm:xi-binomial-toeplitz-comoving-delta-scale-law`. On the comoving slice
`w = (1 - δ)/(1 + δ)` with `0 < δ < 1`, the logarithmic scale is positive and dominates `δ`, the
depth proxy is exactly the reciprocal-scale budget `c / δ`, and the generic scale-depth exchange
wrapper transfers these concrete bounds unchanged. -/
theorem paper_xi_binomial_toeplitz_comoving_delta_scale_law (δ c : ℝ) (hc : 1 < c) :
    0 < δ ∧ δ < 1 →
      xi_binomial_toeplitz_comoving_delta_scale_law_w δ = (1 - δ) / (1 + δ) ∧
      xi_binomial_toeplitz_comoving_delta_scale_law_Lambda δ = Real.log ((1 + δ) / (1 - δ)) ∧
      δ ≤ xi_binomial_toeplitz_comoving_delta_scale_law_Lambda δ ∧
      δ * xi_binomial_toeplitz_comoving_delta_scale_law_m δ c = c ∧
      0 < xi_binomial_toeplitz_comoving_delta_scale_law_m δ c ∧
      (δ ≤ xi_binomial_toeplitz_comoving_delta_scale_law_Lambda δ ∧
        0 < xi_binomial_toeplitz_comoving_delta_scale_law_m δ c ∧
        1 < c) := by
  rintro ⟨hδ0, hδ1⟩
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hpos_add : 0 < 1 + δ := by linarith
  have hpos_sub : 0 < 1 - δ := by linarith
  have hratio_pos : 0 < (1 + δ) / (1 - δ) := div_pos hpos_add hpos_sub
  have hdepth_pos : 0 < xi_binomial_toeplitz_comoving_delta_scale_law_m δ c := by
    exact div_pos (lt_trans zero_lt_one hc) hδ0
  have hdepth_scale : δ * xi_binomial_toeplitz_comoving_delta_scale_law_m δ c = c := by
    calc
      δ * xi_binomial_toeplitz_comoving_delta_scale_law_m δ c = δ * (c / δ) := by
        rfl
      _ = c := by
        field_simp [hδne]
  have hleft :
      1 - (((1 + δ) / (1 - δ))⁻¹) = 2 * δ / (1 + δ) := by
    field_simp [hpos_add.ne', hpos_sub.ne']
    ring
  have hdelta_le_frac : δ ≤ 2 * δ / (1 + δ) := by
    rw [le_div_iff₀ hpos_add]
    nlinarith
  have hdelta_le_lambda :
      δ ≤ xi_binomial_toeplitz_comoving_delta_scale_law_Lambda δ := by
    have hbasic : 1 - (((1 + δ) / (1 - δ))⁻¹) ≤ Real.log ((1 + δ) / (1 - δ)) :=
      Real.one_sub_inv_le_log_of_pos hratio_pos
    calc
      δ ≤ 2 * δ / (1 + δ) := hdelta_le_frac
      _ = 1 - (((1 + δ) / (1 - δ))⁻¹) := hleft.symm
      _ ≤ xi_binomial_toeplitz_comoving_delta_scale_law_Lambda δ := by
        simpa [xi_binomial_toeplitz_comoving_delta_scale_law_Lambda] using hbasic
  have hgeneric :=
    paper_xi_binomial_toeplitz_scale_depth_exchange
      (δ ≤ xi_binomial_toeplitz_comoving_delta_scale_law_Lambda δ)
      (0 < xi_binomial_toeplitz_comoving_delta_scale_law_m δ c)
      (1 < c)
      hdelta_le_lambda hdepth_pos hc
  refine ⟨rfl, rfl, hdelta_le_lambda, hdepth_scale, hdepth_pos, ?_⟩
  simpa using hgeneric

end

end Omega.Zeta
