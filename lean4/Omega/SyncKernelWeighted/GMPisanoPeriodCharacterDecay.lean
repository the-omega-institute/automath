import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Normalized character sum obtained by iterating a one-period twisted contraction factor. -/
def gm_pisano_period_character_decay_normalized_character_sum
    (period m : ℕ) (onePeriodRatio : ℝ) : ℝ :=
  onePeriodRatio ^ (m / period)

/-- Concrete one-period spectral contraction package. -/
def gm_pisano_period_character_decay_one_period_contraction
    (c onePeriodRatio : ℝ) : Prop :=
  0 ≤ onePeriodRatio ∧ onePeriodRatio ≤ Real.exp (-c)

/-- Paper label: `thm:gm-pisano-period-character-decay`.
Once the twisted transfer operator contracts by the factor `exp (-c)` over one Pisano period, the
normalized character sum decays exponentially with the number of completed periods. -/
theorem paper_gm_pisano_period_character_decay
    (period blocks : ℕ) (c onePeriodRatio : ℝ)
    (hperiod : 0 < period)
    (hcontract : gm_pisano_period_character_decay_one_period_contraction c onePeriodRatio) :
    gm_pisano_period_character_decay_normalized_character_sum period (period * blocks)
        onePeriodRatio ≤
      Real.exp (-c * blocks) := by
  rcases hcontract with ⟨hratio_nonneg, hratio_le⟩
  rw [gm_pisano_period_character_decay_normalized_character_sum]
  rw [Nat.mul_div_cancel_left blocks hperiod]
  have hpow : onePeriodRatio ^ blocks ≤ (Real.exp (-c)) ^ blocks := by
    induction blocks with
    | zero =>
        simp
    | succ n ih =>
        calc
          onePeriodRatio ^ (n + 1) = onePeriodRatio ^ n * onePeriodRatio := by rw [pow_succ]
          _ ≤ onePeriodRatio ^ n * Real.exp (-c) :=
            mul_le_mul_of_nonneg_left hratio_le (pow_nonneg hratio_nonneg _)
          _ ≤ (Real.exp (-c)) ^ n * Real.exp (-c) :=
            mul_le_mul_of_nonneg_right ih (by positivity)
          _ = (Real.exp (-c)) ^ (n + 1) := by rw [pow_succ]
  calc
    onePeriodRatio ^ blocks ≤ (Real.exp (-c)) ^ blocks := hpow
    _ = Real.exp ((blocks : ℝ) * (-c)) := by
      symm
      exact Real.exp_nat_mul (-c) blocks
    _ = Real.exp (-c * blocks) := by ring_nf

end Omega.SyncKernelWeighted
