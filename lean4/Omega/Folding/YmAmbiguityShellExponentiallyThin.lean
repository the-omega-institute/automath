import Omega.Core.Fib
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Folding

private theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by positivity)]

private theorem sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := by positivity
  nlinarith [sqrt_three_sq, hsqrt_nonneg]

private theorem one_add_sqrt_three_le_sq : 1 + Real.sqrt 3 ≤ Real.sqrt 3 ^ 2 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := by positivity
  nlinarith [sqrt_three_sq, hsqrt_nonneg]

private theorem fib_shift_two_le_sqrt_three_pow_pair :
    ∀ k : ℕ,
      (Nat.fib (k + 4) : ℝ) ≤ Real.sqrt 3 ^ (k + 2) ∧
        (Nat.fib (k + 5) : ℝ) ≤ Real.sqrt 3 ^ (k + 3)
  | 0 => by
      constructor
      · norm_num [sqrt_three_sq]
      · have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := by positivity
        have : 5 ≤ Real.sqrt 3 ^ 3 := by
          nlinarith [sqrt_three_sq, hsqrt_nonneg]
        simpa using this
  | k + 1 => by
      rcases fib_shift_two_le_sqrt_three_pow_pair k with ⟨hk4, hk5⟩
      constructor
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk5
      · have hrecNat : Nat.fib (k + 6) = Nat.fib (k + 5) + Nat.fib (k + 4) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Omega.fib_succ_succ' (k + 4)
        have hrec : (Nat.fib (k + 6) : ℝ) = (Nat.fib (k + 5) : ℝ) + (Nat.fib (k + 4) : ℝ) := by
          exact_mod_cast hrecNat
        calc
          (Nat.fib (k + 6) : ℝ) = (Nat.fib (k + 5) : ℝ) + (Nat.fib (k + 4) : ℝ) := hrec
          _ ≤ Real.sqrt 3 ^ (k + 3) + Real.sqrt 3 ^ (k + 2) := by gcongr
          _ = Real.sqrt 3 ^ (k + 2) * (1 + Real.sqrt 3) := by ring
          _ ≤ Real.sqrt 3 ^ (k + 2) * Real.sqrt 3 ^ 2 := by
            have hpow_nonneg : 0 ≤ Real.sqrt 3 ^ (k + 2) := by positivity
            exact mul_le_mul_of_nonneg_left one_add_sqrt_three_le_sq hpow_nonneg
          _ = Real.sqrt 3 ^ (k + 4) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (pow_add (Real.sqrt 3) (k + 2) 2).symm

private theorem fib_shift_two_le_sqrt_three_pow (n : ℕ) (hn : 2 ≤ n) :
    (Nat.fib (n + 2) : ℝ) ≤ Real.sqrt 3 ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (fib_shift_two_le_sqrt_three_pow_pair k).1

/-- Paper: `cor:Ym-ambiguity-shell-exponentially-thin`. -/
theorem paper_Ym_ambiguity_shell_exponentially_thin (Namb : ℕ → ℕ)
    (hNamb : ∀ n, Namb n ≤ Nat.fib (n + 2)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ n ≥ 2, (Namb n : ℝ) / (2 : ℝ) ^ n ≤ Real.exp (-ε * n) := by
  refine ⟨Real.log ((2 : ℝ) / Real.sqrt 3), ?_, ?_⟩
  · have hsqrt_pos : 0 < Real.sqrt 3 := by positivity
    have hgt : 1 < (2 : ℝ) / Real.sqrt 3 := by
      rw [one_lt_div hsqrt_pos]
      exact sqrt_three_lt_two
    exact Real.log_pos hgt
  · intro n hn
    have hNamb' : (Namb n : ℝ) ≤ Nat.fib (n + 2) := by
      exact_mod_cast hNamb n
    have hFib : (Nat.fib (n + 2) : ℝ) ≤ Real.sqrt 3 ^ n := fib_shift_two_le_sqrt_three_pow n hn
    have hbound : (Namb n : ℝ) ≤ Real.sqrt 3 ^ n := hNamb'.trans hFib
    have hsqrt_ne : Real.sqrt 3 ≠ 0 := by positivity
    have hquot_pos : 0 < (2 : ℝ) / Real.sqrt 3 := by positivity
    have hbase : Real.exp (-Real.log ((2 : ℝ) / Real.sqrt 3)) = Real.sqrt 3 / 2 := by
      rw [← Real.log_inv, Real.exp_log (inv_pos.mpr hquot_pos)]
      field_simp [hsqrt_ne]
    calc
      (Namb n : ℝ) / (2 : ℝ) ^ n ≤ (Real.sqrt 3 ^ n) / (2 : ℝ) ^ n := by
        gcongr
      _ = (Real.sqrt 3 / 2) ^ n := by rw [← div_pow]
      _ = Real.exp (-Real.log ((2 : ℝ) / Real.sqrt 3) * n) := by
        rw [Real.exp_mul, hbase, Real.rpow_natCast]

end Omega.Folding
