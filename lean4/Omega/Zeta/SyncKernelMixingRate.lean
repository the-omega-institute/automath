import Mathlib.Tactic

namespace Omega.Zeta.SyncKernelMixingRate

/-- Sync kernel state count.
    prop:sync-kernel-explicit-syncword-mixing-rate -/
def syncKernelStateCount : ℕ := 10

/-- 3⁵ = 243.
    prop:sync-kernel-explicit-syncword-mixing-rate -/
theorem three_pow_five : (3 : ℕ) ^ 5 = 243 := by norm_num

/-- Mixing rate: 242/243 = 1 - 1/243.
    prop:sync-kernel-explicit-syncword-mixing-rate -/
theorem mixing_rate_eq : (242 : ℚ) / 243 = 1 - 1 / 243 := by norm_num

/-- Mixing rate is positive: 0 < 242/243.
    prop:sync-kernel-explicit-syncword-mixing-rate -/
theorem mixing_rate_pos : (0 : ℚ) < 242 / 243 := by norm_num

/-- Mixing rate is less than 1: 242/243 < 1.
    prop:sync-kernel-explicit-syncword-mixing-rate -/
theorem mixing_rate_lt_one : (242 : ℚ) / 243 < 1 := by norm_num

/-- Mixing rate is strictly between 0 and 1.
    prop:sync-kernel-explicit-syncword-mixing-rate -/
theorem mixing_rate_mem_Ioo : (0 : ℚ) < 242 / 243 ∧ (242 : ℚ) / 243 < 1 :=
  ⟨mixing_rate_pos, mixing_rate_lt_one⟩

/-- After 10 blocks the mixing decay is below 96%: (242/243)^10 < 96/100.
    prop:sync-kernel-explicit-syncword-mixing-rate -/
theorem mixing_decay_ten_blocks : ((242 : ℚ) / 243) ^ 10 < 96 / 100 := by norm_num

/-- Paper package: sync kernel mixing rate seeds and decay bound.
    prop:sync-kernel-explicit-syncword-mixing-rate -/
theorem paper_sync_kernel_mixing_rate :
    (3 : ℕ) ^ 5 = 243 ∧
    (242 : ℚ) / 243 = 1 - 1 / 243 ∧
    (0 : ℚ) < 242 / 243 ∧
    (242 : ℚ) / 243 < 1 ∧
    ((242 : ℚ) / 243) ^ 10 < 96 / 100 :=
  ⟨three_pow_five, mixing_rate_eq, mixing_rate_pos, mixing_rate_lt_one,
   mixing_decay_ten_blocks⟩

end Omega.Zeta.SyncKernelMixingRate
