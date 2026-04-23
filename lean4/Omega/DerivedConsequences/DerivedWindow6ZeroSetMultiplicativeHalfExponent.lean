import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import Omega.Folding.Entropy
import Omega.Folding.FoldZeroWindow6DensitySharpExponent

open Filter Topology
open scoped goldenRatio

namespace Omega.DerivedConsequences

/-- The rigid window-`6` zero-set envelopes both have multiplicative exponent
`(1 / 2) * log φ` on the subsequence `m = 6n + 4`. -/
def derived_window6_zero_set_multiplicative_half_exponent_statement : Prop :=
  Tendsto
      (fun n : ℕ => Real.log (Nat.fib (3 * n + 3) : ℝ) / (((6 * n + 4 : ℕ) : ℝ)))
      atTop (nhds ((1 / 2 : ℝ) * Real.log Real.goldenRatio)) ∧
    Tendsto
      (fun n : ℕ =>
        Real.log ((((6 * n + 6).divisors.card * Nat.fib (3 * n + 3) : ℕ) : ℝ)) /
          (((6 * n + 4 : ℕ) : ℝ)))
      atTop (nhds ((1 / 2 : ℝ) * Real.log Real.goldenRatio))

private theorem derived_window6_zero_set_multiplicative_half_exponent_ratio_tendsto_half :
    Tendsto
      (fun n : ℕ => (((3 * n + 1 : ℕ) : ℝ)) / (((6 * n + 4 : ℕ) : ℝ)))
      atTop (nhds (1 / 2 : ℝ)) := by
  have hzero :
      Tendsto (fun n : ℕ => (1 : ℝ) / (((6 * n + 4 : ℕ) : ℝ))) atTop (nhds 0) := by
    change Tendsto (((fun m : ℕ => (1 : ℝ) / (m : ℝ)) ∘ fun n : ℕ => 6 * n + 4)) atTop (nhds 0)
    have hshift : Tendsto (fun n : ℕ => 6 * n + 4) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      filter_upwards [eventually_ge_atTop b] with n hn
      omega
    exact (tendsto_const_div_atTop_nhds_zero_nat 1).comp hshift
  have hEq :
      (fun n : ℕ => (((3 * n + 1 : ℕ) : ℝ)) / (((6 * n + 4 : ℕ) : ℝ))) =
        fun n : ℕ => (1 / 2 : ℝ) - 1 / (((6 * n + 4 : ℕ) : ℝ)) := by
    funext n
    have hden : (((6 * n + 4 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hden]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring_nf
  rw [hEq]
  simpa using tendsto_const_nhds.sub hzero

private theorem derived_window6_zero_set_multiplicative_half_exponent_ratio_tendsto_one :
    Tendsto
      (fun n : ℕ => (((6 * n + 6 : ℕ) : ℝ)) / (((6 * n + 4 : ℕ) : ℝ)))
      atTop (nhds (1 : ℝ)) := by
  have hEq :
      (fun n : ℕ => (((6 * n + 6 : ℕ) : ℝ)) / (((6 * n + 4 : ℕ) : ℝ))) =
        fun n : ℕ => (1 : ℝ) + 2 / (((6 * n + 4 : ℕ) : ℝ)) := by
    funext n
    have hden : (((6 * n + 4 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hden]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring_nf
  rw [hEq]
  have hshift : Tendsto (fun n : ℕ => 6 * n + 4) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  simpa using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add
      ((tendsto_const_div_atTop_nhds_zero_nat 2).comp hshift)

private theorem derived_window6_zero_set_multiplicative_half_exponent_lower :
    Tendsto
      (fun n : ℕ => Real.log (Nat.fib (3 * n + 3) : ℝ) / (((6 * n + 4 : ℕ) : ℝ)))
      atTop (nhds ((1 / 2 : ℝ) * Real.log Real.goldenRatio)) := by
  rcases Omega.Folding.paper_fold_zero_window6_density_sharp_exponent with ⟨_, _, hsmall, _⟩
  have hEq :
      (fun n : ℕ => Real.log (Nat.fib (3 * n + 3) : ℝ) / (((6 * n + 4 : ℕ) : ℝ))) =
        fun n : ℕ =>
          (Real.log (Nat.fib (3 * n + 3) : ℝ) / (((3 * n + 1 : ℕ) : ℝ))) *
            ((((3 * n + 1 : ℕ) : ℝ)) / (((6 * n + 4 : ℕ) : ℝ))) := by
    funext n
    have hmid : (((3 * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hmid]
  rw [hEq]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    hsmall.mul derived_window6_zero_set_multiplicative_half_exponent_ratio_tendsto_half

private theorem derived_window6_zero_set_multiplicative_half_exponent_log_linear :
    Tendsto
      (fun n : ℕ => Real.log (((6 * n + 6 : ℕ) : ℝ)) / (((6 * n + 4 : ℕ) : ℝ)))
      atTop (nhds 0) := by
  have hmain :
      Tendsto
        (fun n : ℕ => Real.log (((6 * n + 6 : ℕ) : ℝ)) / (((6 * n + 6 : ℕ) : ℝ)))
        atTop (nhds 0) := by
    have hshift_nat : Tendsto (fun n : ℕ => 6 * n + 6) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      filter_upwards [eventually_ge_atTop b] with n hn
      omega
    have hlin :
        Tendsto (fun n : ℕ => (((6 * n + 6 : ℕ) : ℝ))) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp hshift_nat
    simpa [pow_one] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hlin
  have hEq :
      (fun n : ℕ => Real.log (((6 * n + 6 : ℕ) : ℝ)) / (((6 * n + 4 : ℕ) : ℝ))) =
        fun n : ℕ =>
          (Real.log (((6 * n + 6 : ℕ) : ℝ)) / (((6 * n + 6 : ℕ) : ℝ))) *
            ((((6 * n + 6 : ℕ) : ℝ)) / (((6 * n + 4 : ℕ) : ℝ))) := by
    funext n
    have hmid : (((6 * n + 6 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hmid]
  rw [hEq]
  simpa [zero_mul] using
    hmain.mul derived_window6_zero_set_multiplicative_half_exponent_ratio_tendsto_one

private theorem derived_window6_zero_set_multiplicative_half_exponent_divisor_log :
    Tendsto
      (fun n : ℕ => Real.log (((6 * n + 6).divisors.card : ℕ) : ℝ) / (((6 * n + 4 : ℕ) : ℝ)))
      atTop (nhds 0) := by
  refine Omega.Entropy.tendsto_zero_of_nonneg_le_of_tendsto_zero
    (fun n : ℕ => Real.log (((6 * n + 6).divisors.card : ℕ) : ℝ) / (((6 * n + 4 : ℕ) : ℝ)))
    (fun n : ℕ => Real.log (((6 * n + 6 : ℕ) : ℝ)) / (((6 * n + 4 : ℕ) : ℝ)))
    ?_ ?_ derived_window6_zero_set_multiplicative_half_exponent_log_linear
  · intro n
    have hcard_one_nat : 1 ≤ (6 * n + 6).divisors.card := by
      apply Nat.succ_le_of_lt
      exact Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨Nat.one_dvd _, by omega⟩⟩
    have hcard_one : (1 : ℝ) ≤ ((((6 * n + 6).divisors.card : ℕ) : ℝ)) := by
      exact_mod_cast hcard_one_nat
    exact div_nonneg (Real.log_nonneg hcard_one) (by positivity)
  · intro n
    have hcard_one_nat : 1 ≤ (6 * n + 6).divisors.card := by
      apply Nat.succ_le_of_lt
      exact Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨Nat.one_dvd _, by omega⟩⟩
    have hcard_pos : 0 < ((((6 * n + 6).divisors.card : ℕ) : ℝ)) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hcard_one_nat)
    have hcard_le : (6 * n + 6).divisors.card ≤ 6 * n + 6 := by
      simpa using Nat.card_divisors_le_self (6 * n + 6)
    have hlog_le :
        Real.log ((((6 * n + 6).divisors.card : ℕ) : ℝ)) ≤
          Real.log (((6 * n + 6 : ℕ) : ℝ)) := by
      exact Real.log_le_log hcard_pos (by exact_mod_cast hcard_le)
    exact div_le_div_of_nonneg_right hlog_le (by positivity)

/-- Paper label: `thm:derived-window6-zero-set-multiplicative-half-exponent`. -/
theorem paper_derived_window6_zero_set_multiplicative_half_exponent :
    derived_window6_zero_set_multiplicative_half_exponent_statement := by
  refine ⟨derived_window6_zero_set_multiplicative_half_exponent_lower, ?_⟩
  have hEq :
      (fun n : ℕ =>
        Real.log ((((6 * n + 6).divisors.card * Nat.fib (3 * n + 3) : ℕ) : ℝ)) /
          (((6 * n + 4 : ℕ) : ℝ))) =
        fun n : ℕ =>
          Real.log (((6 * n + 6).divisors.card : ℕ) : ℝ) / (((6 * n + 4 : ℕ) : ℝ)) +
            Real.log (Nat.fib (3 * n + 3) : ℝ) / (((6 * n + 4 : ℕ) : ℝ)) := by
    funext n
    have hcard_pos : 0 < ((((6 * n + 6).divisors.card : ℕ) : ℝ)) := by
      norm_num
    have hfib_pos : 0 < (Nat.fib (3 * n + 3) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (by omega)
    rw [Nat.cast_mul, Real.log_mul hcard_pos.ne' hfib_pos.ne', add_div]
  rw [hEq]
  simpa using derived_window6_zero_set_multiplicative_half_exponent_divisor_log.add
    derived_window6_zero_set_multiplicative_half_exponent_lower

end Omega.DerivedConsequences
