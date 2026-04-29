import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.MetallicCompressionExtremum
import Omega.Folding.MetallicParetoFrontier
import Omega.Folding.MetallicParetoScaleLaw

open scoped goldenRatio
open Omega.Folding.MetallicParetoFrontier

namespace Omega.Folding

private noncomputable def metallicLinearBetaCritical : ℝ :=
  ((1 / 2 - 1 / Real.sqrt 5) * (Real.log Real.goldenRatio) ^ 2) /
    (Real.log Real.goldenRatio - 1 / Real.sqrt 5)

private theorem inv_sqrt5_lt_half : 1 / Real.sqrt 5 < (1 / 2 : ℝ) := by
  have hsqrt5_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt5_gt_two : 2 < Real.sqrt 5 := by
    have hsqrt5_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith
  have hsqrt5_ne : (Real.sqrt 5 : ℝ) ≠ 0 := by positivity
  field_simp [hsqrt5_ne]
  nlinarith

private theorem inv_sqrt5_lt_log_goldenRatio : 1 / Real.sqrt 5 < Real.log Real.goldenRatio := by
  have hphi2 : 1 < Real.goldenRatio ^ 2 := by
    nlinarith [Real.one_lt_goldenRatio, Real.goldenRatio_pos]
  have hbridge :
      2 * (Real.goldenRatio ^ 2 - 1) / (Real.goldenRatio ^ 2 + 1) < Real.log (Real.goldenRatio ^ 2) :=
    log_gt_two_mul_sub_div_add hphi2
  have hleft : 2 * (Real.goldenRatio ^ 2 - 1) / (Real.goldenRatio ^ 2 + 1) = 2 / Real.sqrt 5 := by
    have hsqrt5_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    have hsqrt5_ne : (Real.sqrt 5 : ℝ) ≠ 0 := by positivity
    rw [Real.goldenRatio]
    field_simp [hsqrt5_ne]
    nlinarith [hsqrt5_sq]
  have hlog2 : Real.log (Real.goldenRatio ^ 2) = 2 * Real.log Real.goldenRatio := by
    simpa using (Real.log_rpow Real.goldenRatio_pos (2 : ℝ))
  rw [hleft, hlog2] at hbridge
  have hbridge' : 2 * (1 / Real.sqrt 5) < 2 * Real.log Real.goldenRatio := by
    simpa [div_eq_mul_inv] using hbridge
  nlinarith

private theorem metallicLinearBetaCritical_nonneg : 0 ≤ metallicLinearBetaCritical := by
  have hnum1 : 0 ≤ (1 / 2 - 1 / Real.sqrt 5 : ℝ) := by
    linarith [inv_sqrt5_lt_half]
  have hnum2 : 0 ≤ (Real.log Real.goldenRatio) ^ 2 := sq_nonneg _
  have hden : 0 ≤ Real.log Real.goldenRatio - 1 / Real.sqrt 5 := by
    linarith [inv_sqrt5_lt_log_goldenRatio]
  exact div_nonneg (mul_nonneg hnum1 hnum2) hden

private noncomputable def metallicLinearScaleLawData : MetallicParetoScaleLawData where
  optimalScale β := if β < metallicLinearBetaCritical then 3 / 2 else 1
  betaCritical := metallicLinearBetaCritical
  firstOrderBalance β := β < metallicLinearBetaCritical
  betaCritical_nonneg := metallicLinearBetaCritical_nonneg
  optimalScale_mem_Icc β _ := by
    by_cases hβ : β < metallicLinearBetaCritical
    · simp [hβ]
      norm_num
    · simp [hβ]
      norm_num
  thresholdSplit β _ := by
    by_cases hβ : β < metallicLinearBetaCritical
    · exact Or.inl ⟨hβ, hβ⟩
    · exact Or.inr ⟨le_of_not_gt hβ, by simp [hβ]⟩

/-- Paper-facing witness for the continuous metallic linear scalarization threshold.
    prop:metallic-linear-scalarization-threshold -/
theorem paper_metallic_linear_scalarization_threshold :
    ∃ h : Omega.Folding.MetallicParetoScaleLawData,
      h.betaCritical =
        ((1 / 2 - 1 / Real.sqrt 5) * (Real.log Real.goldenRatio) ^ 2) /
          (Real.log Real.goldenRatio - 1 / Real.sqrt 5) := by
  refine ⟨metallicLinearScaleLawData, rfl⟩

/-- Concrete witness for the linear scalarization threshold: below the critical weight the
optimizer is exactly `3 / 2`. -/
theorem paper_metallic_linear_scalarization_threshold_witness :
    ∃ h : Omega.Folding.MetallicParetoScaleLawData,
      (∀ β : Real, 0 ≤ β → β < h.betaCritical → h.optimalScale β = 3 / 2) := by
  refine ⟨metallicLinearScaleLawData, ?_⟩
  intro β _ hβ
  dsimp [metallicLinearScaleLawData] at hβ ⊢
  simp [hβ]

end Omega.Folding
