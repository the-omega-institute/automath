import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The Perron parameter used in the finite-RH real-input-40 package. -/
def finite_rh_40_lambda : ℝ :=
  Real.goldenRatio ^ (2 : ℕ)

/-- The unique negative square-root branch that lands on the critical line. -/
def finite_rh_40_critical_branch : ℝ :=
  -Real.sqrt finite_rh_40_lambda

/-- The reciprocal negative square-root branch. -/
def finite_rh_40_inverse_branch : ℝ :=
  -(Real.sqrt finite_rh_40_lambda)⁻¹

/-- The audited nonzero spectrum of the real-input-40 kernel. -/
def finite_rh_40_audited_spectrum : List ℝ :=
  [finite_rh_40_lambda, 1, 1, finite_rh_40_lambda⁻¹, finite_rh_40_critical_branch,
    finite_rh_40_inverse_branch, 1, 1, -1]

/-- The Perron main coefficient appearing in the finite explicit formula. -/
def finite_rh_40_main_coeff : ℝ :=
  finite_rh_40_lambda * Real.log finite_rh_40_lambda / (finite_rh_40_lambda - 1)

/-- Concrete data package for the finite-RH real-input-40 spectrum audit. -/
structure finite_rh_40_data where
  auditedSpectrum : List ℝ
  auditedSpectrum_eq : auditedSpectrum = finite_rh_40_audited_spectrum

namespace finite_rh_40_data

/-- The real part forced by solving `lambda^(-s) * mu = 1` at the level of absolute values. -/
def finite_rh_40_real_part (_D : finite_rh_40_data) (μ : ℝ) : ℝ :=
  Real.log |μ| / Real.log finite_rh_40_lambda

/-- The audited pole equation in real-part form. -/
def finite_rh_40_pole_equation (D : finite_rh_40_data) (μ : ℝ) : Prop :=
  finite_rh_40_lambda ^ (-(D.finite_rh_40_real_part μ)) * |μ| = 1

/-- The open strip `0 < Re(s) < 1` for the audited spectrum. -/
def finite_rh_40_open_strip (D : finite_rh_40_data) (μ : ℝ) : Prop :=
  μ ∈ D.auditedSpectrum ∧ 0 < D.finite_rh_40_real_part μ ∧ D.finite_rh_40_real_part μ < 1

end finite_rh_40_data

open finite_rh_40_data

/-- The finite-RH real-input-40 package records the audited spectrum, every nonzero branch solves
the logarithmic pole equation `lambda^(-s) * |mu| = 1`, the `-sqrt(lambda)` branch lies in the
open strip, and no other audited branch does. -/
def finite_rh_40_statement (D : finite_rh_40_data) : Prop :=
  D.auditedSpectrum = finite_rh_40_audited_spectrum ∧
    (∀ μ : ℝ, μ ≠ 0 → D.finite_rh_40_pole_equation μ) ∧
    D.finite_rh_40_open_strip finite_rh_40_critical_branch ∧
    ∀ μ : ℝ, D.finite_rh_40_open_strip μ → μ = finite_rh_40_critical_branch

private lemma finite_rh_40_lambda_gt_one : 1 < finite_rh_40_lambda := by
  rw [finite_rh_40_lambda, Real.goldenRatio_sq]
  nlinarith [Real.one_lt_goldenRatio]

private lemma finite_rh_40_lambda_pos : 0 < finite_rh_40_lambda :=
  lt_trans zero_lt_one finite_rh_40_lambda_gt_one

private lemma finite_rh_40_log_lambda_pos : 0 < Real.log finite_rh_40_lambda :=
  Real.log_pos finite_rh_40_lambda_gt_one

private lemma finite_rh_40_log_lambda_ne_zero : Real.log finite_rh_40_lambda ≠ 0 :=
  finite_rh_40_log_lambda_pos.ne'

private lemma finite_rh_40_sqrt_lambda_pos : 0 < Real.sqrt finite_rh_40_lambda :=
  Real.sqrt_pos.mpr finite_rh_40_lambda_pos

lemma finite_rh_40_main_coeff_pos : 0 < finite_rh_40_main_coeff := by
  unfold finite_rh_40_main_coeff
  exact div_pos (mul_pos finite_rh_40_lambda_pos finite_rh_40_log_lambda_pos)
    (by linarith [finite_rh_40_lambda_gt_one])

private lemma finite_rh_40_real_part_of_nonzero (D : finite_rh_40_data) (μ : ℝ) (hμ : μ ≠ 0) :
    finite_rh_40_lambda ^ (D.finite_rh_40_real_part μ) = |μ| := by
  unfold finite_rh_40_data.finite_rh_40_real_part
  apply (Real.mul_log_eq_log_iff finite_rh_40_lambda_pos (abs_pos.mpr hμ)).mp
  field_simp [finite_rh_40_log_lambda_ne_zero]
  rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ finite_rh_40_log_lambda_ne_zero, mul_one]

private lemma finite_rh_40_pole_equation_of_nonzero (D : finite_rh_40_data) (μ : ℝ) (hμ : μ ≠ 0) :
    D.finite_rh_40_pole_equation μ := by
  have hpow : finite_rh_40_lambda ^ (D.finite_rh_40_real_part μ) = |μ| :=
    finite_rh_40_real_part_of_nonzero D μ hμ
  unfold finite_rh_40_data.finite_rh_40_pole_equation
  rw [Real.rpow_neg finite_rh_40_lambda_pos.le, hpow]
  exact inv_mul_cancel₀ (abs_pos.mpr hμ).ne'

private lemma finite_rh_40_real_part_lambda (D : finite_rh_40_data) :
    D.finite_rh_40_real_part finite_rh_40_lambda = 1 := by
  unfold finite_rh_40_data.finite_rh_40_real_part
  rw [abs_of_pos finite_rh_40_lambda_pos, div_self finite_rh_40_log_lambda_ne_zero]

private lemma finite_rh_40_real_part_one (D : finite_rh_40_data) :
    D.finite_rh_40_real_part 1 = 0 := by
  unfold finite_rh_40_data.finite_rh_40_real_part
  simp

private lemma finite_rh_40_real_part_inv_lambda (D : finite_rh_40_data) :
    D.finite_rh_40_real_part finite_rh_40_lambda⁻¹ = -1 := by
  unfold finite_rh_40_data.finite_rh_40_real_part
  rw [abs_of_pos (inv_pos.mpr finite_rh_40_lambda_pos), Real.log_inv]
  field_simp [finite_rh_40_log_lambda_ne_zero]
  rw [div_self finite_rh_40_log_lambda_ne_zero]

private lemma finite_rh_40_real_part_critical_branch (D : finite_rh_40_data) :
    D.finite_rh_40_real_part finite_rh_40_critical_branch = 1 / 2 := by
  unfold finite_rh_40_data.finite_rh_40_real_part finite_rh_40_critical_branch
  rw [abs_neg, abs_of_pos finite_rh_40_sqrt_lambda_pos, Real.log_sqrt finite_rh_40_lambda_pos.le]
  field_simp [finite_rh_40_log_lambda_ne_zero]
  rw [div_self finite_rh_40_log_lambda_ne_zero]

private lemma finite_rh_40_real_part_inverse_branch (D : finite_rh_40_data) :
    D.finite_rh_40_real_part finite_rh_40_inverse_branch = -1 / 2 := by
  unfold finite_rh_40_data.finite_rh_40_real_part finite_rh_40_inverse_branch
  rw [abs_neg, abs_of_pos (inv_pos.mpr finite_rh_40_sqrt_lambda_pos), Real.log_inv,
    Real.log_sqrt finite_rh_40_lambda_pos.le]
  field_simp [finite_rh_40_log_lambda_ne_zero]
  rw [div_self finite_rh_40_log_lambda_ne_zero]

private lemma finite_rh_40_real_part_neg_one (D : finite_rh_40_data) :
    D.finite_rh_40_real_part (-1) = 0 := by
  unfold finite_rh_40_data.finite_rh_40_real_part
  simp

/-- Paper label: `prop:finite-rh-40`. -/
theorem paper_finite_rh_40 (D : finite_rh_40_data) : finite_rh_40_statement D := by
  refine ⟨D.auditedSpectrum_eq, ?_, ?_, ?_⟩
  · intro μ hμ
    exact finite_rh_40_pole_equation_of_nonzero D μ hμ
  · refine ⟨?_, ?_, ?_⟩
    · rw [D.auditedSpectrum_eq]
      simp [finite_rh_40_audited_spectrum, finite_rh_40_critical_branch]
    · rw [finite_rh_40_real_part_critical_branch D]
      norm_num
    · rw [finite_rh_40_real_part_critical_branch D]
      norm_num
  · intro μ hμ
    rcases hμ with ⟨hmem, hpos, hlt⟩
    rw [D.auditedSpectrum_eq] at hmem
    simp [finite_rh_40_audited_spectrum, finite_rh_40_critical_branch,
      finite_rh_40_inverse_branch] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | hlast
    · rw [finite_rh_40_real_part_lambda D] at hlt
      linarith
    · rw [finite_rh_40_real_part_one D] at hpos
      linarith
    · rw [finite_rh_40_real_part_inv_lambda D] at hpos
      linarith
    · rfl
    · change 0 < D.finite_rh_40_real_part finite_rh_40_inverse_branch at hpos
      rw [finite_rh_40_real_part_inverse_branch D] at hpos
      linarith
    · rcases hlast with rfl | rfl
      · rw [finite_rh_40_real_part_one D] at hpos
        linarith
      · rw [finite_rh_40_real_part_neg_one D] at hpos
        linarith

end

end Omega.SyncKernelRealInput
