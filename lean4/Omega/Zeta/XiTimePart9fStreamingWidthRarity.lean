import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9f-streaming-width-rarity`. -/
theorem paper_xi_time_part9f_streaming_width_rarity (m S n : ℕ)
    (branchProgramCount modelCount probability : ℝ) (hmodel : 0 < modelCount)
    (hS : 1 ≤ S) (hn : 1 ≤ n)
    (hcount : branchProgramCount ≤ (n : ℝ) ^ S * (S : ℝ) ^ (2 * S * m))
    (hunion : probability ≤ branchProgramCount / modelCount) :
    probability ≤ Real.exp
      (2 * (S : ℝ) * (m : ℝ) * Real.log (S : ℝ) + (S : ℝ) * Real.log (n : ℝ) -
        Real.log modelCount) := by
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hS_pos : 0 < (S : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hS)
  have hquot :
      branchProgramCount / modelCount ≤
        ((n : ℝ) ^ S * (S : ℝ) ^ (2 * S * m)) / modelCount :=
    div_le_div_of_nonneg_right hcount hmodel.le
  have hexp :
      ((n : ℝ) ^ S * (S : ℝ) ^ (2 * S * m)) / modelCount =
        Real.exp
          (2 * (S : ℝ) * (m : ℝ) * Real.log (S : ℝ) +
              (S : ℝ) * Real.log (n : ℝ) -
            Real.log modelCount) := by
    have hnum_pos :
        0 < (n : ℝ) ^ S * (S : ℝ) ^ (2 * S * m) :=
      mul_pos (pow_pos hn_pos _) (pow_pos hS_pos _)
    calc
      ((n : ℝ) ^ S * (S : ℝ) ^ (2 * S * m)) / modelCount =
          Real.exp
            (Real.log (((n : ℝ) ^ S * (S : ℝ) ^ (2 * S * m)) / modelCount)) := by
            rw [Real.exp_log (div_pos hnum_pos hmodel)]
      _ = Real.exp
          (2 * (S : ℝ) * (m : ℝ) * Real.log (S : ℝ) +
              (S : ℝ) * Real.log (n : ℝ) -
            Real.log modelCount) := by
            congr 1
            rw [Real.log_div (ne_of_gt hnum_pos) hmodel.ne',
              Real.log_mul (pow_ne_zero _ hn_pos.ne') (pow_ne_zero _ hS_pos.ne'),
              Real.log_pow, Real.log_pow]
            norm_num [Nat.cast_mul]
            ring
  exact le_trans (le_trans hunion hquot) (by rw [hexp])

end Omega.Zeta
