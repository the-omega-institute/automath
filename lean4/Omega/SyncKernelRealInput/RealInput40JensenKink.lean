import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.FiniteRhJensenFreeEnergy

namespace Omega.SyncKernelRealInput

noncomputable section

/-- Spectral radius used for the real-input-40 Jensen free-energy model. -/
def real_input_40_jensen_kink_lambda : ℝ := 4

lemma real_input_40_jensen_kink_lambda_gt_one : 1 < real_input_40_jensen_kink_lambda := by
  norm_num [real_input_40_jensen_kink_lambda]

lemma real_input_40_jensen_kink_log_sqrt_lambda :
    Real.log (Real.sqrt real_input_40_jensen_kink_lambda) =
      (1 / 2 : ℝ) * Real.log real_input_40_jensen_kink_lambda := by
  have hnonneg : 0 ≤ real_input_40_jensen_kink_lambda := by
    norm_num [real_input_40_jensen_kink_lambda]
  calc
    Real.log (Real.sqrt real_input_40_jensen_kink_lambda) =
        Real.log real_input_40_jensen_kink_lambda / 2 := Real.log_sqrt hnonneg
    _ = (1 / 2 : ℝ) * Real.log real_input_40_jensen_kink_lambda := by ring

/-- Jensen free energy obtained from the finite-RH package for the two contributing spectral
moduli `λ` and `sqrt λ`. -/
noncomputable def real_input_40_jensen_kink_G_M : ℝ → ℝ :=
  Classical.choose
    (Omega.SyncKernelWeighted.paper_finite_rh_jensen_free_energy
      real_input_40_jensen_kink_lambda
      real_input_40_jensen_kink_lambda_gt_one
      [real_input_40_jensen_kink_lambda, Real.sqrt real_input_40_jensen_kink_lambda])

/-- Piecewise linear profile on `0 ≤ σ ≤ 1`: the `sqrt λ` term drops out after `σ = 1/2`. -/
def real_input_40_jensen_kink_piecewise (σ : ℝ) : ℝ :=
  if σ ≤ 1 / 2 then
    ((3 / 2 : ℝ) - 2 * σ) * Real.log real_input_40_jensen_kink_lambda
  else
    (1 - σ) * Real.log real_input_40_jensen_kink_lambda

local notation "G_M" => real_input_40_jensen_kink_G_M
local notation "real_input_40_jensen_piecewise" => real_input_40_jensen_kink_piecewise

section

variable (sigma : ℝ) (h_sigma_nonneg : 0 ≤ sigma) (h_sigma_le_one : sigma ≤ 1)

/-- Paper label: `cor:real-input-40-jensen-kink`. On the strip `0 ≤ σ ≤ 1`, the finite-RH Jensen
free energy has the expected two-branch form, with the `sqrt λ` contribution disappearing exactly
at `σ = 1/2`. -/
theorem paper_real_input_40_jensen_kink
    (h_sigma_nonneg : 0 ≤ sigma) (h_sigma_le_one : sigma ≤ 1) :
    G_M sigma = real_input_40_jensen_piecewise sigma := by
  let _ := h_sigma_nonneg
  have hG :=
    Classical.choose_spec
      (Omega.SyncKernelWeighted.paper_finite_rh_jensen_free_energy
        real_input_40_jensen_kink_lambda
        real_input_40_jensen_kink_lambda_gt_one
        [real_input_40_jensen_kink_lambda, Real.sqrt real_input_40_jensen_kink_lambda])
  have hlog_pos : 0 < Real.log real_input_40_jensen_kink_lambda := by
    simpa using Real.log_pos real_input_40_jensen_kink_lambda_gt_one
  have hlog_nonneg : 0 ≤ Real.log real_input_40_jensen_kink_lambda := le_of_lt hlog_pos
  change
    Classical.choose
        (Omega.SyncKernelWeighted.paper_finite_rh_jensen_free_energy
          real_input_40_jensen_kink_lambda
          real_input_40_jensen_kink_lambda_gt_one
          [real_input_40_jensen_kink_lambda, Real.sqrt real_input_40_jensen_kink_lambda]) sigma =
      real_input_40_jensen_kink_piecewise sigma
  rw [hG sigma, real_input_40_jensen_kink_piecewise]
  by_cases hhalf : sigma ≤ 1 / 2
  · rw [if_pos hhalf]
    simp only [List.map, List.sum_cons, List.sum_nil]
    have hfirst_factor : 0 ≤ 1 - sigma := by linarith
    have hfirst_nonneg :
        0 ≤ Real.log real_input_40_jensen_kink_lambda -
          sigma * Real.log real_input_40_jensen_kink_lambda := by
      have hmul :
          0 ≤ (1 - sigma) * Real.log real_input_40_jensen_kink_lambda :=
        mul_nonneg hfirst_factor hlog_nonneg
      nlinarith
    have hsecond_factor : 0 ≤ (1 / 2 : ℝ) - sigma := by linarith
    have hsecond_nonneg :
        0 ≤ Real.log (Real.sqrt real_input_40_jensen_kink_lambda) -
          sigma * Real.log real_input_40_jensen_kink_lambda := by
      rw [real_input_40_jensen_kink_log_sqrt_lambda]
      have hmul :
          0 ≤ ((1 / 2 : ℝ) - sigma) * Real.log real_input_40_jensen_kink_lambda :=
        mul_nonneg hsecond_factor hlog_nonneg
      nlinarith
    have hsecond_nonneg' :
        0 ≤ Real.log real_input_40_jensen_kink_lambda * (1 / 2) -
          Real.log real_input_40_jensen_kink_lambda * sigma := by
      have hmul :
          0 ≤ Real.log real_input_40_jensen_kink_lambda * ((1 / 2 : ℝ) - sigma) :=
        mul_nonneg hlog_nonneg hsecond_factor
      nlinarith
    rw [max_eq_right hfirst_nonneg]
    simp [real_input_40_jensen_kink_log_sqrt_lambda]
    have hmax_second :
        max 0
            ((2 : ℝ)⁻¹ * Real.log real_input_40_jensen_kink_lambda -
              sigma * Real.log real_input_40_jensen_kink_lambda) =
          (2 : ℝ)⁻¹ * Real.log real_input_40_jensen_kink_lambda -
            sigma * Real.log real_input_40_jensen_kink_lambda := by
      apply max_eq_right
      nlinarith
    rw [hmax_second]
    ring_nf
  · rw [if_neg hhalf]
    simp only [List.map, List.sum_cons, List.sum_nil]
    have hhalf_lt : 1 / 2 < sigma := lt_of_not_ge hhalf
    have hfirst_factor : 0 ≤ 1 - sigma := by linarith
    have hfirst_nonneg :
        0 ≤ Real.log real_input_40_jensen_kink_lambda -
          sigma * Real.log real_input_40_jensen_kink_lambda := by
      have hmul :
          0 ≤ (1 - sigma) * Real.log real_input_40_jensen_kink_lambda :=
        mul_nonneg hfirst_factor hlog_nonneg
      nlinarith
    have hsecond_factor : (1 / 2 : ℝ) - sigma ≤ 0 := by linarith
    have hsecond_nonpos :
        Real.log (Real.sqrt real_input_40_jensen_kink_lambda) -
          sigma * Real.log real_input_40_jensen_kink_lambda ≤ 0 := by
      rw [real_input_40_jensen_kink_log_sqrt_lambda]
      have hmul :
          ((1 / 2 : ℝ) - sigma) * Real.log real_input_40_jensen_kink_lambda ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hsecond_factor hlog_nonneg
      nlinarith
    have hsecond_nonpos' :
        Real.log real_input_40_jensen_kink_lambda * (1 / 2) -
          Real.log real_input_40_jensen_kink_lambda * sigma ≤ 0 := by
      have hmul :
          Real.log real_input_40_jensen_kink_lambda * ((1 / 2 : ℝ) - sigma) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hlog_nonneg hsecond_factor
      nlinarith
    rw [max_eq_right hfirst_nonneg]
    simp [real_input_40_jensen_kink_log_sqrt_lambda]
    have hmax_second :
        max 0
            ((2 : ℝ)⁻¹ * Real.log real_input_40_jensen_kink_lambda -
              sigma * Real.log real_input_40_jensen_kink_lambda) = 0 := by
      apply max_eq_left
      nlinarith
    rw [hmax_second]
    ring_nf

end

end

end Omega.SyncKernelRealInput
