import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.CayleyDepthIdentity

namespace Omega.Zeta

open scoped BigOperators
open Real
open CayleyDepthIdentity

/-- The logarithmic load attached to the off-critical Cayley modulus. -/
noncomputable def xiLogDefectLoad (γ δ x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (cayleyModSq δ γ x)

/-- The quadratic load attached to the same Cayley point. -/
noncomputable def xiQuadraticLoad (γ δ x : ℝ) : ℝ :=
  cayleyDepth δ γ x

/-- The finite-family logarithmic load. -/
noncomputable def xiFiniteFamilyLogDefectLoad {n : ℕ}
    (γ δ : Fin n → ℝ) (m : Fin n → ℕ) (x : ℝ) : ℝ :=
  ∑ j, (m j : ℝ) * xiLogDefectLoad (γ j) (δ j) x

/-- The finite-family quadratic load. -/
noncomputable def xiFiniteFamilyQuadraticLoad {n : ℕ}
    (γ δ : Fin n → ℝ) (m : Fin n → ℕ) (x : ℝ) : ℝ :=
  ∑ j, (m j : ℝ) * xiQuadraticLoad (γ j) (δ j) x

private lemma cayleyModSq_pos_of_half_band {γ δ x : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    0 < cayleyModSq δ γ x := by
  unfold cayleyModSq
  have hnum : 0 < (γ - x) ^ 2 + (1 - δ) ^ 2 := by
    have hsq : 0 ≤ (γ - x) ^ 2 := sq_nonneg _
    have hone : 0 < (1 - δ) ^ 2 := by
      have : 0 < 1 - δ := by linarith
      positivity
    linarith
  have hden : 0 < (γ - x) ^ 2 + (1 + δ) ^ 2 := by positivity
  exact div_pos hnum hden

private lemma cayleyModSq_le_one_of_half_band {γ δ x : ℝ} (hδ : 0 < δ) :
    cayleyModSq δ γ x ≤ 1 := by
  have hdepth_nonneg : 0 ≤ cayleyDepth δ γ x := cayleyDepth_nonneg δ γ x hδ.le
  have hdepth_eq : 1 - cayleyModSq δ γ x = cayleyDepth δ γ x :=
    one_sub_cayleyModSq_eq_cayleyDepth δ γ x hδ
  nlinarith

private lemma cayleyModSq_one_ninth_le {γ δ x : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    1 / 9 ≤ cayleyModSq δ γ x := by
  have hden_ge : (1 + δ) ^ 2 ≤ (γ - x) ^ 2 + (1 + δ) ^ 2 := by
    nlinarith [sq_nonneg (γ - x)]
  have hdepth_le :
      cayleyDepth δ γ x ≤ 4 * δ / (1 + δ) ^ 2 := by
    unfold cayleyDepth
    have hnonneg : 0 ≤ 4 * δ := by nlinarith
    have hpos : 0 < (1 + δ) ^ 2 := by
      have : 0 < 1 + δ := by linarith
      positivity
    exact div_le_div_of_nonneg_left hnonneg hpos hden_ge
  have hdepth_le' : cayleyDepth δ γ x ≤ 8 / 9 := by
    refine le_trans hdepth_le ?_
    have hdelta_nonneg : 0 ≤ δ := le_of_lt hδ
    have hpos : (1 + δ) ^ 2 ≠ 0 := by
      have : 0 < 1 + δ := by linarith
      positivity
    field_simp [hpos]
    nlinarith
  have hdepth_eq : 1 - cayleyModSq δ γ x = cayleyDepth δ γ x :=
    one_sub_cayleyModSq_eq_cayleyDepth δ γ x hδ
  nlinarith

private lemma xiLogDefect_pointwise_bounds (γ δ x : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    (1 / 2 : ℝ) * xiQuadraticLoad γ δ x ≤ xiLogDefectLoad γ δ x ∧
      xiLogDefectLoad γ δ x ≤ (9 / 2 : ℝ) * xiQuadraticLoad γ δ x := by
  have hu : 0 < cayleyModSq δ γ x := cayleyModSq_pos_of_half_band hδ hδ'
  have hu_le_one : cayleyModSq δ γ x ≤ 1 := cayleyModSq_le_one_of_half_band hδ
  have hu_ge_nine : 1 / 9 ≤ cayleyModSq δ γ x := cayleyModSq_one_ninth_le hδ hδ'
  have hdepth_eq :
      xiQuadraticLoad γ δ x = 1 - cayleyModSq δ γ x := by
    unfold xiQuadraticLoad
    linarith [one_sub_cayleyModSq_eq_cayleyDepth δ γ x hδ]
  constructor
  · have hlog : Real.log (cayleyModSq δ γ x) ≤ cayleyModSq δ γ x - 1 :=
      Real.log_le_sub_one_of_pos hu
    unfold xiLogDefectLoad
    rw [hdepth_eq]
    nlinarith
  · have hlog_inv :
        Real.log ((cayleyModSq δ γ x)⁻¹) ≤ (cayleyModSq δ γ x)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.2 hu)
    have hlog_inv' : -Real.log (cayleyModSq δ γ x) ≤ (cayleyModSq δ γ x)⁻¹ - 1 := by
      simpa [Real.log_inv] using hlog_inv
    have hu_inv_bound : (cayleyModSq δ γ x)⁻¹ ≤ 9 := by
      have hmul : (1 : ℝ) ≤ 9 * cayleyModSq δ γ x := by
        nlinarith
      exact (inv_le_iff_one_le_mul₀ hu).2 hmul
    have hu_gap_nonneg : 0 ≤ 1 - cayleyModSq δ γ x := by
      nlinarith
    have haux : (cayleyModSq δ γ x)⁻¹ - 1 ≤ 9 * (1 - cayleyModSq δ γ x) := by
      have hmul := mul_le_mul_of_nonneg_left hu_inv_bound hu_gap_nonneg
      have hrew :
          (cayleyModSq δ γ x)⁻¹ - 1 = (1 - cayleyModSq δ γ x) * (cayleyModSq δ γ x)⁻¹ := by
        field_simp [hu.ne']
      rw [hrew]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    unfold xiLogDefectLoad
    rw [hdepth_eq]
    have hmain : -Real.log (cayleyModSq δ γ x) ≤ 9 * (1 - cayleyModSq δ γ x) :=
      le_trans hlog_inv' haux
    nlinarith

/-- In the half-band `0 < δ ≤ 1/2`, the logarithmic defect load and the quadratic load are
pointwise comparable with constants `1/2` and `9/2`; summing termwise gives the finite-family
comparison.
    thm:xi-logdefect-vs-quadratic-load-two-sided -/
theorem paper_xi_logdefect_vs_quadratic_load_two_sided {n : ℕ}
    (γ δ : Fin n → ℝ) (m : Fin n → ℕ) (hδ : ∀ j, 0 < δ j ∧ δ j ≤ 1 / 2) :
    (∀ j x, (1 / 2 : ℝ) * xiQuadraticLoad (γ j) (δ j) x ≤ xiLogDefectLoad (γ j) (δ j) x ∧
      xiLogDefectLoad (γ j) (δ j) x ≤ (9 / 2 : ℝ) * xiQuadraticLoad (γ j) (δ j) x) ∧
      (∀ x, (1 / 2 : ℝ) * xiFiniteFamilyQuadraticLoad γ δ m x ≤
        xiFiniteFamilyLogDefectLoad γ δ m x ∧
          xiFiniteFamilyLogDefectLoad γ δ m x ≤
            (9 / 2 : ℝ) * xiFiniteFamilyQuadraticLoad γ δ m x) := by
  refine ⟨?_, ?_⟩
  · intro j x
    exact xiLogDefect_pointwise_bounds (γ j) (δ j) x (hδ j).1 (hδ j).2
  · intro x
    constructor
    · unfold xiFiniteFamilyQuadraticLoad xiFiniteFamilyLogDefectLoad
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum ?_
      intro j hj
      have hm : 0 ≤ (m j : ℝ) := by positivity
      have hpoint := (xiLogDefect_pointwise_bounds (γ j) (δ j) x (hδ j).1 (hδ j).2).1
      have hmul := mul_le_mul_of_nonneg_left hpoint hm
      nlinarith
    · unfold xiFiniteFamilyQuadraticLoad xiFiniteFamilyLogDefectLoad
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum ?_
      intro j hj
      have hm : 0 ≤ (m j : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left
        (xiLogDefect_pointwise_bounds (γ j) (δ j) x (hδ j).1 (hδ j).2).2 hm
      nlinarith

end Omega.Zeta
