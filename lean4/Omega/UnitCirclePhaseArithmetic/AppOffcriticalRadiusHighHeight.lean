import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic
import Omega.Zeta.AppOffcriticalRadiusCompression

open Filter
open scoped Topology

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `cor:app-offcritical-radius-high-height`. -/
theorem paper_app_offcritical_radius_high_height (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun γ : ℝ => γ ^ 2 * Omega.Zeta.appOffcriticalBoundaryDepth γ δ) atTop
        (nhds (4 * δ)) ∧
      Tendsto (fun γ : ℝ => γ ^ 2 * (1 - Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ))) atTop
        (nhds (2 * δ)) := by
  let c : ℝ := (δ + 1) ^ 2
  have hγsq : Tendsto (fun γ : ℝ => γ ^ 2) atTop atTop := by
    exact tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hden : Tendsto (fun γ : ℝ => γ ^ 2 + c) atTop atTop := by
    exact tendsto_atTop_add_const_right _ _ hγsq
  have hinv : Tendsto (fun γ : ℝ => (γ ^ 2 + c)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hcorr : Tendsto (fun γ : ℝ => c * (γ ^ 2 + c)⁻¹) atTop (𝓝 0) := by
    simpa [c] using (tendsto_const_nhds (x := c)).mul hinv
  have hratio : Tendsto (fun γ : ℝ => 1 - c * (γ ^ 2 + c)⁻¹) atTop (𝓝 1) := by
    simpa [sub_eq_add_neg] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hcorr
  have hdepth_scaled_aux :
      Tendsto (fun γ : ℝ => (4 * δ) * (1 - c * (γ ^ 2 + c)⁻¹)) atTop (𝓝 (4 * δ)) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => 4 * δ) atTop (𝓝 (4 * δ))).mul hratio
  have hdepth_scaled :
      Tendsto (fun γ : ℝ => γ ^ 2 * Omega.Zeta.appOffcriticalBoundaryDepth γ δ) atTop
        (nhds (4 * δ)) := by
    have hdepth_eq :
        ∀ γ : ℝ,
          γ ^ 2 * Omega.Zeta.appOffcriticalBoundaryDepth γ δ =
            (4 * δ) * (1 - c * (γ ^ 2 + c)⁻¹) := by
      intro γ
      rw [Omega.Zeta.appOffcriticalBoundaryDepth_closed_form γ δ hδ]
      have hden_ne : γ ^ 2 + c ≠ 0 := by
        have : 0 < γ ^ 2 + c := by
          dsimp [c]
          positivity
        exact ne_of_gt this
      field_simp [hden_ne]
      ring
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun γ => (hdepth_eq γ).symm) hdepth_scaled_aux
  have hdepth_zero_aux : Tendsto (fun γ : ℝ => (4 * δ) * (γ ^ 2 + c)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => 4 * δ) atTop (𝓝 (4 * δ))).mul hinv
  have hdepth_zero : Tendsto (fun γ : ℝ => Omega.Zeta.appOffcriticalBoundaryDepth γ δ) atTop (𝓝 0) := by
    have hdepth_zero_eq :
        ∀ γ : ℝ,
          Omega.Zeta.appOffcriticalBoundaryDepth γ δ = (4 * δ) * (γ ^ 2 + c)⁻¹ := by
      intro γ
      rw [Omega.Zeta.appOffcriticalBoundaryDepth_closed_form γ δ hδ]
      simp [c, div_eq_mul_inv]
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun γ => (hdepth_zero_eq γ).symm)
      hdepth_zero_aux
  have hmodsq_one : Tendsto (fun γ : ℝ => Omega.Zeta.appOffcriticalModSq γ δ) atTop (𝓝 1) := by
    have haux :
        Tendsto (fun γ : ℝ => 1 - Omega.Zeta.appOffcriticalBoundaryDepth γ δ) atTop (𝓝 (1 - 0)) := by
      exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hdepth_zero
    simpa [Omega.Zeta.appOffcriticalBoundaryDepth] using haux
  have hsqrt_one :
      Tendsto (fun γ : ℝ => Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ)) atTop (nhds 1) := by
    have hsqrt_aux :
        Tendsto (fun γ : ℝ => Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ)) atTop
          (𝓝 (Real.sqrt 1)) := by
      exact Real.continuous_sqrt.continuousAt.tendsto.comp hmodsq_one
    simpa using hsqrt_aux
  have hden_inv :
      Tendsto (fun γ : ℝ => (1 + Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ))⁻¹) atTop
        (nhds ((2 : ℝ)⁻¹)) := by
    have hden_to_two :
        Tendsto (fun γ : ℝ => 1 + Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ)) atTop
          (nhds 2) := by
      have hden_to_two_aux :
          Tendsto (fun γ : ℝ => 1 + Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ)) atTop
            (nhds (1 + 1)) := by
        exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hsqrt_one
      convert hden_to_two_aux using 1
      norm_num
    exact hden_to_two.inv₀ (by norm_num : (2 : ℝ) ≠ 0)
  have hsecond_aux :
      Tendsto
        (fun γ : ℝ =>
          (γ ^ 2 * Omega.Zeta.appOffcriticalBoundaryDepth γ δ) *
            (1 + Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ))⁻¹)
        atTop (nhds (2 * δ)) := by
    have hprod :
        Tendsto
          (fun γ : ℝ =>
            (γ ^ 2 * Omega.Zeta.appOffcriticalBoundaryDepth γ δ) *
              (1 + Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ))⁻¹)
          atTop (nhds ((4 * δ) * ((2 : ℝ)⁻¹))) := by
      exact hdepth_scaled.mul hden_inv
    convert hprod using 1
    ring_nf
  have hsecond :
      Tendsto (fun γ : ℝ => γ ^ 2 * (1 - Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ))) atTop
        (nhds (2 * δ)) := by
    refine Filter.Tendsto.congr' ?_ hsecond_aux
    refine Filter.Eventually.of_forall ?_
    intro γ
    let m := Omega.Zeta.appOffcriticalModSq γ δ
    have hm_nonneg : 0 ≤ m := by
      dsimp [m]
      unfold Omega.Zeta.appOffcriticalModSq Omega.Zeta.CayleyDepthIdentity.cayleyModSq
      positivity
    have hone_add_ne : 1 + Real.sqrt m ≠ 0 := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
      linarith
    have hone_sub :
        1 - Real.sqrt m = (1 - m) / (1 + Real.sqrt m) := by
      field_simp [hone_add_ne]
      ring_nf
      rw [Real.sq_sqrt hm_nonneg]
    show γ ^ 2 * Omega.Zeta.appOffcriticalBoundaryDepth γ δ *
        (1 + Real.sqrt (Omega.Zeta.appOffcriticalModSq γ δ))⁻¹ =
      γ ^ 2 * (1 - Real.sqrt m)
    rw [hone_sub, Omega.Zeta.appOffcriticalBoundaryDepth]
    ring
  exact ⟨hdepth_scaled, hsecond⟩

end Omega.UnitCirclePhaseArithmetic
