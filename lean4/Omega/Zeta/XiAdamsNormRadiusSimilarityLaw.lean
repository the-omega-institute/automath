import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Omega.Zeta.PhaseImplementationRankLimit

open Filter Topology

namespace Omega.Zeta

/-- The common asymptotic factor in the Adams norm transport law. -/
noncomputable def xiAdamsCommonFactor (n : ℕ) (δ : ℝ) : ℝ :=
  (((n : ℝ) ^ 2) + (1 + δ) ^ 2) / (4 * δ)

/-- The radius-dependent logarithmic weight. -/
noncomputable def xiAdamsRadiusWeight (r : ℝ) : ℝ :=
  Real.log (1 / r ^ 2)

/-- The explicit threshold scale `m_star`. -/
noncomputable def xiAdamsMStar (n : ℕ) (δ r : ℝ) : ℕ :=
  Nat.ceil (xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r)

lemma xiAdamsRadiusWeight_pos {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    0 < xiAdamsRadiusWeight r := by
  unfold xiAdamsRadiusWeight
  have hlog : Real.log r < 0 := Real.log_neg hr₀ hr₁
  calc
    Real.log (1 / r ^ 2) = -2 * Real.log r := by
      rw [show 1 / r ^ 2 = (r ^ 2)⁻¹ by simp [one_div]]
      rw [Real.log_inv, pow_two, Real.log_mul hr₀.ne' hr₀.ne']
      ring
    _ > 0 := by nlinarith

lemma xiAdamsCommonFactor_pos (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 < xiAdamsCommonFactor n δ := by
  unfold xiAdamsCommonFactor
  positivity

lemma xiAdamsMStar_sandwich (n : ℕ) {δ r : ℝ} (hδ : 0 < δ) (hr₀ : 0 < r) (hr₁ : r < 1) :
    xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r ≤ xiAdamsMStar n δ r ∧
      (xiAdamsMStar n δ r : ℝ) < xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r + 1 := by
  have hnonneg : 0 ≤ xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r := by
    have hcf : 0 < xiAdamsCommonFactor n δ := xiAdamsCommonFactor_pos n hδ
    have hw : 0 < xiAdamsRadiusWeight r := xiAdamsRadiusWeight_pos hr₀ hr₁
    nlinarith
  constructor
  · exact Nat.le_ceil _
  · exact Nat.ceil_lt_add_one hnonneg

lemma tendsto_xiAdamsCommonFactor_atTop {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => xiAdamsCommonFactor n δ) atTop atTop := by
  have hpowReal : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := by
    simpa using (tendsto_pow_atTop (n := 2) (by norm_num : (2 : ℕ) ≠ 0))
  have hpow : Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)) atTop atTop :=
    hpowReal.comp tendsto_natCast_atTop_atTop
  have hadd : Tendsto (fun n : ℕ => ((n : ℝ) ^ 2) + (1 + δ) ^ 2) atTop atTop := by
    exact tendsto_atTop_add_const_right _ _ hpow
  have hscale :
      Tendsto (fun n : ℕ => ((4 * δ)⁻¹) * (((n : ℝ) ^ 2) + (1 + δ) ^ 2)) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity : 0 < (4 * δ)⁻¹) hadd
  simpa [xiAdamsCommonFactor, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscale

lemma tendsto_xiAdamsScaleRatio {δ r₁ r₂ : ℝ} (hδ : 0 < δ)
    (_hr₁₀ : 0 < r₁) (_hr₁₁ : r₁ < 1) (hr₂₀ : 0 < r₂) (hr₂₁ : r₂ < 1) :
    Tendsto
      (fun n : ℕ =>
        (xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r₁) /
          (xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r₂))
      atTop (𝓝 (xiAdamsRadiusWeight r₁ / xiAdamsRadiusWeight r₂)) := by
  have hcf_pos : ∀ n : ℕ, 0 < xiAdamsCommonFactor n δ := fun n => xiAdamsCommonFactor_pos n hδ
  have hw₂ : 0 < xiAdamsRadiusWeight r₂ := xiAdamsRadiusWeight_pos hr₂₀ hr₂₁
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.Eventually.of_forall fun n : ℕ => hcf_pos n] with n hn
  field_simp [hn.ne', hw₂.ne']

/-- The ceiling definition of `m_star` stays within one unit of its asymptotic proxy, and the
ratio for two target radii converges to the ratio of the corresponding logarithmic weights. -/
theorem paper_xi_adams_norm_radius_similarity_law
    (δ r₁ r₂ : ℝ) (hδ : 0 < δ)
    (hr₁ : 0 < r₁ ∧ r₁ < 1) (hr₂ : 0 < r₂ ∧ r₂ < 1) :
    (∀ n : ℕ,
      xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r₁ ≤ xiAdamsMStar n δ r₁ ∧
        (xiAdamsMStar n δ r₁ : ℝ) < xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r₁ + 1 ∧
        xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r₂ ≤ xiAdamsMStar n δ r₂ ∧
        (xiAdamsMStar n δ r₂ : ℝ) < xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r₂ + 1) ∧
      Tendsto
        (fun n : ℕ =>
          (xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r₁) /
            (xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r₂))
        atTop (𝓝 (xiAdamsRadiusWeight r₁ / xiAdamsRadiusWeight r₂)) := by
  have hsandwich :
      ∀ n : ℕ,
        xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r₁ ≤ xiAdamsMStar n δ r₁ ∧
          (xiAdamsMStar n δ r₁ : ℝ) < xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r₁ + 1 ∧
          xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r₂ ≤ xiAdamsMStar n δ r₂ ∧
          (xiAdamsMStar n δ r₂ : ℝ) < xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r₂ + 1 := by
    intro n
    obtain ⟨h₁lo, h₁hi⟩ := xiAdamsMStar_sandwich n hδ hr₁.1 hr₁.2
    obtain ⟨h₂lo, h₂hi⟩ := xiAdamsMStar_sandwich n hδ hr₂.1 hr₂.2
    exact ⟨h₁lo, h₁hi, h₂lo, h₂hi⟩
  have hratio :
      Tendsto
        (fun n : ℕ =>
          (xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r₁) /
            (xiAdamsCommonFactor n δ * xiAdamsRadiusWeight r₂))
        atTop (𝓝 (xiAdamsRadiusWeight r₁ / xiAdamsRadiusWeight r₂)) :=
    tendsto_xiAdamsScaleRatio hδ hr₁.1 hr₁.2 hr₂.1 hr₂.2
  constructor
  · exact hsandwich
  · exact hratio

end Omega.Zeta
