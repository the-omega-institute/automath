import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinRenyiDivergenceLimit

namespace Omega.Zeta

noncomputable section

lemma xi_time_part70e_renyi_curve_negative_odd_sampling_golden_sum :
    Real.goldenRatio + Real.goldenRatio ^ (-1 : ℝ) = Real.sqrt 5 := by
  have hphi : Real.goldenRatio ≠ 0 := Real.goldenRatio_ne_zero
  have hsqrt_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
    norm_num [Real.sq_sqrt]
  have hphi_def : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  rw [Real.rpow_neg_one]
  rw [hphi_def]
  field_simp [hphi, show (2 : ℝ) ≠ 0 by norm_num]
  nlinarith [hsqrt_sq, Real.sqrt_nonneg 5]

lemma xi_time_part70e_renyi_curve_negative_odd_sampling_ne_one
    (α : ℝ) (hα : α ≠ 1) :
    Real.rpow 5 ((α - 1) / 2) *
        Real.rpow Real.goldenRatio (2 - 2 * α) *
        Real.exp ((α - 1) * Omega.Folding.foldBinRenyiDivergenceLimitConstant α) =
      (Real.goldenRatio + Real.rpow Real.goldenRatio (-α)) / Real.sqrt 5 := by
  have h5 : (0 : ℝ) < 5 := by norm_num
  have hsqrt5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 h5
  have hphi : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hsum : 0 < Real.goldenRatio + Real.goldenRatio ^ (-α) :=
    add_pos hphi (Real.rpow_pos_of_pos hphi _)
  have hsub : α - 1 ≠ 0 := sub_ne_zero.mpr hα
  rw [Omega.Folding.foldBinRenyiDivergenceLimitConstant, if_neg hα]
  rw [show
      (α - 1) *
          (((2 * α - 2) * Real.log Real.goldenRatio +
                  Real.log (Real.goldenRatio + Real.goldenRatio ^ (-α)) -
                α * Real.log (Real.sqrt 5)) /
              (α - 1)) =
        (2 * α - 2) * Real.log Real.goldenRatio +
          Real.log (Real.goldenRatio + Real.goldenRatio ^ (-α)) -
        α * Real.log (Real.sqrt 5) by
    field_simp [hsub]]
  rw [show
      (2 * α - 2) * Real.log Real.goldenRatio +
            Real.log (Real.goldenRatio + Real.goldenRatio ^ (-α)) -
          α * Real.log (Real.sqrt 5) =
        Real.log Real.goldenRatio * (2 * α - 2) +
            Real.log (Real.goldenRatio + Real.goldenRatio ^ (-α)) -
          Real.log (Real.sqrt 5) * α by
        ring_nf]
  rw [Real.exp_sub]
  rw [Real.exp_add]
  rw [← Real.rpow_def_of_pos hphi]
  rw [Real.exp_log hsum]
  rw [← Real.rpow_def_of_pos hsqrt5]
  rw [show (2 : ℝ) - 2 * α = -(2 * α - 2) by ring]
  simp_rw [Real.rpow_eq_pow]
  rw [Real.rpow_neg (le_of_lt hphi)]
  rw [Real.rpow_def_of_pos h5]
  rw [show Real.log 5 * ((α - 1) / 2) = Real.log (Real.sqrt 5) * (α - 1) by
    have hlog : Real.log 5 = 2 * Real.log (Real.sqrt 5) := by
      calc
        Real.log 5 = Real.log ((Real.sqrt 5) ^ 2) := by
          congr
          exact (Real.sq_sqrt (le_of_lt h5)).symm
        _ = 2 * Real.log (Real.sqrt 5) := by
          rw [Real.log_pow]
          norm_num
    rw [hlog]
    ring]
  rw [← Real.rpow_def_of_pos hsqrt5]
  rw [Real.rpow_sub hsqrt5]
  have hphi_pow_ne : Real.goldenRatio ^ (2 * α - 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hphi _)
  have hsqrt_pow_ne : (Real.sqrt 5) ^ α ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hsqrt5 _)
  field_simp [hphi_pow_ne, hsqrt_pow_ne, hsqrt5.ne']; simp [Real.rpow_one]

/-- Paper label: `thm:xi-time-part70e-renyi-curve-negative-odd-sampling`. -/
theorem paper_xi_time_part70e_renyi_curve_negative_odd_sampling (α : ℝ) (hα : 0 < α) :
    Real.rpow 5 ((α - 1) / 2) * Real.rpow Real.goldenRatio (2 - 2 * α) *
        Real.exp ((α - 1) * Omega.Folding.foldBinRenyiDivergenceLimitConstant α) =
      (Real.goldenRatio + Real.rpow Real.goldenRatio (-α)) / Real.sqrt 5 := by
  by_cases h : α = 1
  · subst h
    simp
    rw [xi_time_part70e_renyi_curve_negative_odd_sampling_golden_sum]
    field_simp [show (Real.sqrt 5 : ℝ) ≠ 0 by positivity]
  · exact xi_time_part70e_renyi_curve_negative_odd_sampling_ne_one α h

end

end Omega.Zeta
