import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The weighted depth profile `H(x₀)` attached to a finite family of depths. -/
noncomputable def xiDepthProfile {n : ℕ} (w h : Fin n → ℝ) : ℝ :=
  ∑ j, w j * h j

/-- The endpoint defect potential `Φ(x₀)` as the weighted sum of the endpoint defects
`-log (1 - hⱼ)`. -/
noncomputable def xiEndpointDefectPotential {n : ℕ} (w h : Fin n → ℝ) : ℝ :=
  ∑ j, w j * (-Real.log (1 - h j))

lemma xi_neg_log_lower_quadratic {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u < 1) :
    u + u ^ 2 / 2 ≤ -Real.log (1 - u) := by
  have hsum :
      ∑ i ∈ Finset.range 2, u ^ (i + 1) / ((i : ℝ) + 1) ≤ -Real.log (1 - u) := by
    exact sum_le_hasSum (s := Finset.range 2)
      (f := fun i : ℕ => u ^ (i + 1) / ((i : ℝ) + 1))
      (by intro i hi; positivity)
      (Real.hasSum_pow_div_log_of_abs_lt_one (x := u) (by simpa [abs_of_nonneg hu₀] using hu₁))
  have hsum' := hsum
  norm_num [Finset.sum_range_succ, pow_two] at hsum'
  simpa [pow_two] using hsum'

lemma xi_neg_log_upper_linear {u η : ℝ} (hu₀ : 0 ≤ u) (hη : 0 < η) (huη : u ≤ 1 - η) :
    -Real.log (1 - u) ≤ u / η := by
  have hone_sub_u : 0 < 1 - u := by
    linarith
  have hlog :
      -Real.log (1 - u) ≤ u / (1 - u) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hone_sub_u)
    have hloginv : -Real.log (1 - u) = Real.log ((1 - u)⁻¹) := by
      rw [Real.log_inv]
    rw [hloginv]
    have hfrac : (1 - u)⁻¹ - 1 = u / (1 - u) := by
      field_simp [hone_sub_u.ne']
      ring
    exact h.trans_eq hfrac
  have hη_le : η ≤ 1 - u := by
    linarith
  have hfrac : u / (1 - u) ≤ u / η := by
    have hηne : η ≠ 0 := ne_of_gt hη
    have hone_sub_ne : 1 - u ≠ 0 := ne_of_gt hone_sub_u
    field_simp [hηne, hone_sub_ne]
    nlinarith
  exact hlog.trans hfrac

lemma xi_weighted_cauchy_sq {n : ℕ} (w h : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) :
    (∑ j, w j * h j) ^ (2 : ℕ) ≤ (∑ j, w j) * ∑ j, w j * h j ^ (2 : ℕ) := by
  simpa [pow_two, Real.sq_sqrt, hw, mul_assoc, mul_left_comm, mul_comm] using
    (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (f := fun j => Real.sqrt (w j))
      (g := fun j => Real.sqrt (w j) * h j))

/-- The endpoint defect potential controls the depth profile from both sides: the lower bound comes
from the quadratic truncation of `-log (1 - u)` together with weighted Cauchy-Schwarz, while the
upper bound comes from `log x ≤ x - 1` applied to `(1 - u)⁻¹` and the uniform gap `η`.
    prop:xi-limit-defect-potential-vs-depth-profile -/
theorem paper_xi_limit_defect_potential_vs_depth_profile {n : ℕ} (w h : Fin n → ℝ)
    {η κ : ℝ} (hw : ∀ j, 0 ≤ w j) (hκ : ∑ j, w j = κ) (hκ_pos : 0 < κ) (hη : 0 < η)
    (hh₀ : ∀ j, 0 ≤ h j) (hhη : ∀ j, h j ≤ 1 - η) :
    xiDepthProfile w h + (xiDepthProfile w h) ^ 2 / (2 * κ) ≤ xiEndpointDefectPotential w h ∧
      xiEndpointDefectPotential w h ≤ xiDepthProfile w h / η := by
  have hterm_lower :
      ∀ j : Fin n, w j * (h j + h j ^ 2 / 2) ≤ w j * (-Real.log (1 - h j)) := by
    intro j
    refine mul_le_mul_of_nonneg_left ?_ (hw j)
    exact xi_neg_log_lower_quadratic (hh₀ j) (lt_of_le_of_lt (hhη j) (by linarith))
  have hterm_upper :
      ∀ j : Fin n, w j * (-Real.log (1 - h j)) ≤ w j * (h j / η) := by
    intro j
    refine mul_le_mul_of_nonneg_left ?_ (hw j)
    exact xi_neg_log_upper_linear (hh₀ j) hη (hhη j)
  have hsum_lower :
      ∑ j, w j * (h j + h j ^ 2 / 2) ≤ xiEndpointDefectPotential w h := by
    simpa [xiEndpointDefectPotential] using Finset.sum_le_sum fun j _ => hterm_lower j
  have hsum_upper :
      xiEndpointDefectPotential w h ≤ ∑ j, w j * (h j / η) := by
    simpa [xiEndpointDefectPotential] using Finset.sum_le_sum fun j _ => hterm_upper j
  have hcauchy :
      (xiDepthProfile w h) ^ (2 : ℕ) ≤ κ * ∑ j, w j * h j ^ (2 : ℕ) := by
    simpa [xiDepthProfile, hκ] using xi_weighted_cauchy_sq w h hw
  have hdiv :
      (xiDepthProfile w h) ^ 2 / κ ≤ ∑ j, w j * h j ^ (2 : ℕ) := by
    have hκne : κ ≠ 0 := ne_of_gt hκ_pos
    field_simp [hκne]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcauchy
  have hquad :
      (xiDepthProfile w h) ^ 2 / (2 * κ) ≤ (∑ j, w j * h j ^ (2 : ℕ)) / 2 := by
    have hκne : κ ≠ 0 := ne_of_gt hκ_pos
    calc
      (xiDepthProfile w h) ^ 2 / (2 * κ) = ((xiDepthProfile w h) ^ 2 / κ) / 2 := by
        field_simp [hκne]
      _ ≤ (∑ j, w j * h j ^ (2 : ℕ)) / 2 := by
        gcongr
  constructor
  · calc
      xiDepthProfile w h + (xiDepthProfile w h) ^ 2 / (2 * κ)
          ≤ xiDepthProfile w h + (∑ j, w j * h j ^ (2 : ℕ)) / 2 := by
              gcongr
      _ = ∑ j, w j * (h j + h j ^ 2 / 2) := by
            rw [xiDepthProfile, Finset.sum_div, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ ≤ xiEndpointDefectPotential w h := hsum_lower
  · calc
      xiEndpointDefectPotential w h ≤ ∑ j, w j * (h j / η) := hsum_upper
      _ = xiDepthProfile w h / η := by
            calc
              ∑ j, w j * (h j / η) = ∑ j, (w j * h j) / η := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                field_simp [ne_of_gt hη]
              _ = xiDepthProfile w h / η := by
                rw [xiDepthProfile, Finset.sum_div]

end Omega.Zeta
