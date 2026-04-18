import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Omega.CircleDimension.CayleyPoissonWindowIdentity

namespace Omega.CircleDimension

open scoped intervalIntegral
open MeasureTheory Real

private theorem cayley_cauchy_line_integral (s : ℝ) (hs : 0 < s) :
    (∫ γ : ℝ, s / (γ ^ 2 + s ^ 2)) = Real.pi := by
  have hs_ne : s ≠ 0 := ne_of_gt hs
  calc
    (∫ γ : ℝ, s / (γ ^ 2 + s ^ 2)) =
        ∫ γ : ℝ, (1 / s) * ((1 + (γ / s) ^ 2)⁻¹) := by
          apply integral_congr_ae
          filter_upwards with γ
          field_simp [hs_ne]
          ring
    _ = (1 / s) * ∫ γ : ℝ, ((1 + (γ / s) ^ 2)⁻¹) := by
          rw [integral_const_mul]
    _ = (1 / s) * (|s| • ∫ y : ℝ, (1 + y ^ 2)⁻¹) := by
          rw [Measure.integral_comp_div (g := fun y : ℝ => (1 + y ^ 2)⁻¹) s]
    _ = (1 / s) * (|s| * ∫ y : ℝ, (1 + y ^ 2)⁻¹) := by
          rw [smul_eq_mul]
    _ = Real.pi := by
          rw [integral_univ_inv_one_add_sq, abs_of_pos hs]
          field_simp [hs_ne]

/-- The total mass of the positive Cayley-Poisson window over the symmetric line family is
`2πδ`. The proof swaps the `γ` and `s` integrations and evaluates the inner Cauchy integral. -/
theorem paper_cdim_cayley_window_mass_conservation (lam : ℝ) (δ : ℝ) (_hlam : 0 < lam)
    (hδ : 0 < δ)
    (hδlt : δ < lam) : (∫ γ : ℝ, ∫ s in (lam - δ)..(lam + δ), s / (γ ^ 2 + s ^ 2)) =
    2 * Real.pi * δ := by
  let a : ℝ := lam - δ
  let b : ℝ := lam + δ
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hb : 0 < b := by
    dsimp [b]
    linarith
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have ha_ne : a ≠ 0 := ne_of_gt ha
  let S : Set (ℝ × ℝ) := Set.Ioc a b ×ˢ Set.univ
  have hγ_base : Integrable fun x : ℝ => (1 + x ^ 2)⁻¹ := by
    simpa using integrable_inv_one_add_sq
  have hγ : Integrable fun γ : ℝ => b / (γ ^ 2 + a ^ 2) := by
    have hscaled : Integrable fun γ : ℝ => (1 + (γ / a) ^ 2)⁻¹ := by
      simpa [div_eq_mul_inv] using
        (Integrable.comp_mul_right' (g := fun x : ℝ => (1 + x ^ 2)⁻¹) hγ_base
          (R := a⁻¹) (inv_ne_zero ha_ne))
    have hconst :
        Integrable fun γ : ℝ => (b / a ^ 2) * ((1 + (γ / a) ^ 2)⁻¹) :=
      hscaled.const_mul (b / a ^ 2)
    refine hconst.congr ?_
    filter_upwards with γ
    field_simp [ha_ne]
    ring
  have hIoc : Integrable (Set.indicator (Set.Ioc a b) (fun _ : ℝ => (1 : ℝ))) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (by simp [Real.volume_Ioc])
  have hbound :
      Integrable fun z : ℝ × ℝ =>
        Set.indicator (Set.Ioc a b) (fun _ : ℝ => (1 : ℝ)) z.1 * (b / (z.2 ^ 2 + a ^ 2)) :=
    hIoc.mul_prod hγ
  have hindicator :
      Integrable
        (Set.indicator S fun z : ℝ × ℝ => z.1 / (z.2 ^ 2 + z.1 ^ 2)) (volume.prod volume) := by
    refine Integrable.mono' hbound ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      measurability
    · filter_upwards with z
      by_cases hz : z.1 ∈ Set.Ioc a b
      · have hz_pos : 0 < z.1 := lt_trans ha hz.1
        have hz_le : z.1 ≤ b := hz.2
        have hz_sq : a ^ 2 ≤ z.1 ^ 2 := by
          nlinarith [hz.1.le]
        have hden_nonneg : 0 ≤ z.2 ^ 2 + a ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
        have hnum_nonneg : 0 ≤ z.1 := hz_pos.le
        have habs : |z.2 ^ 2 + z.1 ^ 2| = z.2 ^ 2 + z.1 ^ 2 := by
          exact abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
        simp [S, hz, abs_of_nonneg hnum_nonneg, habs]
        have hstep1 : z.1 * (z.2 ^ 2 + a ^ 2) ≤ z.1 * (z.2 ^ 2 + z.1 ^ 2) := by
          gcongr
        have hstep2 : z.1 * (z.2 ^ 2 + z.1 ^ 2) ≤ b * (z.2 ^ 2 + z.1 ^ 2) := by
          gcongr
        have hmul : z.1 * (z.2 ^ 2 + a ^ 2) ≤ b * (z.2 ^ 2 + z.1 ^ 2) :=
          hstep1.trans hstep2
        have hden_pos : 0 < z.2 ^ 2 + z.1 ^ 2 := by
          exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hz_pos)
        have hdena_pos : 0 < z.2 ^ 2 + a ^ 2 := by
          exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos ha)
        exact (div_le_div_iff₀ hden_pos hdena_pos).2 hmul
      · simp [S, hz]
  have hswap_int :
      Integrable (Function.uncurry fun s γ : ℝ => s / (γ ^ 2 + s ^ 2))
        ((volume.restrict (Set.uIoc a b)).prod volume) := by
    have hOn :
        IntegrableOn (fun z : ℝ × ℝ => z.1 / (z.2 ^ 2 + z.1 ^ 2)) S (volume.prod volume) := by
      rw [← integrable_indicator_iff (measurableSet_Ioc.prod MeasurableSet.univ)]
      simpa [S] using hindicator
    have hprod :
        (((volume.restrict (Set.Ioc a b)).prod volume : Measure (ℝ × ℝ))) =
          (volume.prod volume).restrict (Set.Ioc a b ×ˢ Set.univ) := by
      simpa [Measure.restrict_univ] using
        (Measure.prod_restrict (μ := volume) (ν := volume) (Set.Ioc a b) Set.univ)
    simpa [IntegrableOn, S, Set.uIoc_of_le hab, Function.uncurry, hprod] using hOn
  rw [← intervalIntegral_integral_swap hswap_int]
  rw [intervalIntegral.integral_of_le hab]
  have hconst_ae :
      (fun s : ℝ => ∫ γ : ℝ, s / (γ ^ 2 + s ^ 2)) =ᵐ[volume.restrict (Set.Ioc a b)]
        fun _ => Real.pi := by
    exact (ae_restrict_iff' measurableSet_Ioc).2 <|
      Filter.Eventually.of_forall fun s hs =>
        cayley_cauchy_line_integral s (lt_trans ha hs.1)
  rw [integral_congr_ae hconst_ae, integral_const]
  simp [hab]
  dsimp [a, b]
  ring

end Omega.CircleDimension
