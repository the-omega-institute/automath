import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Explicit selector-free critical order from the spectral ratio formula in the paper. -/
noncomputable def conclusionSympowerCriticalOrder (ρ η : ℝ) : ℕ :=
  Nat.floor (2 * (1 - Real.log η / Real.log ρ)) + 1

/-- Paper label: `thm:conclusion-sympower-explicit-critical-order`. -/
theorem paper_conclusion_sympower_explicit_critical_order
    (ρ η : ℝ) (hρ : 1 < ρ) (hη0 : 0 < η) (hη : η < ρ) :
    let bCrit := conclusionSympowerCriticalOrder ρ η
    ∀ b : ℕ, bCrit ≤ b → ρ ^ (2 * (b - 1)) * η ^ 2 > ρ ^ b := by
  intro bCrit b hb
  have hb' : conclusionSympowerCriticalOrder ρ η ≤ b := by
    simpa using hb
  have hρ0 : 0 < ρ := lt_trans zero_lt_one hρ
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hb1 : 1 ≤ b := by
    exact le_trans (Nat.succ_le_succ (Nat.zero_le _)) hb'
  have hbound_floor :
      2 * (1 - Real.log η / Real.log ρ) <
        (Nat.floor (2 * (1 - Real.log η / Real.log ρ)) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hb_real : (Nat.floor (2 * (1 - Real.log η / Real.log ρ)) : ℝ) + 1 ≤ b := by
    exact_mod_cast hb'
  have hbound :
      2 * (1 - Real.log η / Real.log ρ) < (b : ℝ) := by
    exact lt_of_lt_of_le hbound_floor hb_real
  have hlin_raw :
      2 * (1 - Real.log η / Real.log ρ) * Real.log ρ < (b : ℝ) * Real.log ρ := by
    exact mul_lt_mul_of_pos_right hbound hlogρ
  have hlin :
      (2 : ℝ) * (Real.log ρ - Real.log η) < (b : ℝ) * Real.log ρ := by
    have hsimp :
        2 * (1 - Real.log η / Real.log ρ) * Real.log ρ =
          (2 : ℝ) * (Real.log ρ - Real.log η) := by
      calc
        2 * (1 - Real.log η / Real.log ρ) * Real.log ρ
            = 2 * ((1 - Real.log η / Real.log ρ) * Real.log ρ) := by ring
        _ = (2 : ℝ) * (Real.log ρ - Real.log η) := by
          field_simp [hlogρ.ne']
    simpa [hsimp] using hlin_raw
  have hleft_pos : 0 < ρ ^ b := by positivity
  have hright_pos : 0 < ρ ^ (2 * (b - 1)) * η ^ 2 := by positivity
  have hlog_goal :
      Real.log (ρ ^ b) < Real.log (ρ ^ (2 * (b - 1)) * η ^ 2) := by
    rw [Real.log_mul (pow_ne_zero _ hρ0.ne') (pow_ne_zero _ hη0.ne')]
    rw [show Real.log (ρ ^ b) = (b : ℝ) * Real.log ρ by
      rw [show ρ ^ b = ρ ^ (b : ℝ) by rw [Real.rpow_natCast], Real.log_rpow hρ0]]
    rw [show Real.log (ρ ^ (2 * (b - 1))) = ((2 * (b - 1) : ℕ) : ℝ) * Real.log ρ by
      rw [show ρ ^ (2 * (b - 1)) = ρ ^ ((2 * (b - 1) : ℕ) : ℝ) by rw [Real.rpow_natCast],
        Real.log_rpow hρ0]]
    rw [show Real.log (η ^ 2) = (2 : ℝ) * Real.log η by
      rw [show η ^ 2 = η ^ (2 : ℝ) by norm_num [Real.rpow_natCast], Real.log_rpow hη0]]
    norm_num [Nat.cast_mul, Nat.cast_sub hb1]
    linarith
  exact (Real.log_lt_log_iff hleft_pos hright_pos).1 hlog_goal

end Omega.Conclusion
