import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.POM

private theorem pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden :
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / Nat.fib (n + 1)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
  rw [Real.inv_goldenRatio]
  simpa using tendsto_fib_div_fib_succ_atTop

private theorem pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_shift :
    Tendsto (fun n : ℕ => (Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
  have h := tendsto_fib_div_fib_succ_atTop.comp (tendsto_add_atTop_nat (1 : ℕ))
  rw [Real.inv_goldenRatio]
  simpa [Nat.add_assoc] using h

private theorem pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_shift2 :
    Tendsto (fun n : ℕ => (Nat.fib (n + 2) : ℝ) / Nat.fib (n + 3)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
  simpa [Nat.add_assoc] using
    pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_shift.comp
      (tendsto_add_atTop_nat (1 : ℕ))

private theorem pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_sq :
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / Nat.fib (n + 2)) atTop
      (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 2)) := by
  have hprod :
      Tendsto
        (fun n : ℕ =>
          ((Nat.fib n : ℝ) / Nat.fib (n + 1)) *
            ((Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)))
        atTop (nhds ((Real.goldenRatio⁻¹ : ℝ) * Real.goldenRatio⁻¹)) := by
    exact
      pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden.mul
        pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_shift
  have hprod' :
      Tendsto
        (fun n : ℕ =>
          ((Nat.fib n : ℝ) / Nat.fib (n + 1)) *
            ((Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)))
        atTop (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 2)) := by
    simpa [pow_two] using hprod
  refine Tendsto.congr' ?_ hprod'
  filter_upwards [Filter.Eventually.of_forall fun _ => True.intro] with n _
  have hfib : (Nat.fib (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos n)))
  field_simp [hfib]

private theorem pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_cube :
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / Nat.fib (n + 3)) atTop
      (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 3)) := by
  have hprod :
      Tendsto
        (fun n : ℕ =>
          ((Nat.fib n : ℝ) / Nat.fib (n + 1)) *
            ((Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) *
              ((Nat.fib (n + 2) : ℝ) / Nat.fib (n + 3)))
        atTop
        (nhds ((Real.goldenRatio⁻¹ : ℝ) * Real.goldenRatio⁻¹ * Real.goldenRatio⁻¹)) := by
    simpa [mul_assoc] using
      pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden.mul
        (pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_shift.mul
          pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_shift2)
  have hprod' :
      Tendsto
        (fun n : ℕ =>
          ((Nat.fib n : ℝ) / Nat.fib (n + 1)) *
            ((Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) *
              ((Nat.fib (n + 2) : ℝ) / Nat.fib (n + 3)))
        atTop (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 3)) := by
    simpa [pow_succ, mul_assoc] using hprod
  refine Tendsto.congr' ?_ hprod'
  filter_upwards [Filter.Eventually.of_forall fun _ => True.intro] with n _
  have hfib1 : (Nat.fib (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos n)))
  have hfib2 : (Nat.fib (n + 2) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos (n + 1))))
  field_simp [hfib1, hfib2]

/-- Paper label: `cor:pom-max-fiber-achievers-hidden-bit-prob-spectrum`. -/
theorem paper_pom_max_fiber_achievers_hidden_bit_prob_spectrum :
    Tendsto (fun k : ℕ => (Nat.fib k : ℝ) / Nat.fib (k + 2)) atTop
        (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 2)) ∧
      Tendsto (fun k : ℕ => (Nat.fib (k + 1) : ℝ) / Nat.fib (k + 2)) atTop
        (nhds (Real.goldenRatio⁻¹ : ℝ)) ∧
      Tendsto (fun k : ℕ => (1 / 2 : ℝ) + (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3)))
        atTop (nhds ((1 / 2 : ℝ) + (Real.goldenRatio⁻¹ : ℝ) ^ 3 / 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_sq
  · exact pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_shift
  · have hdelta :
        Tendsto (fun k : ℕ => (Nat.fib k : ℝ) / (2 * Nat.fib (k + 3))) atTop
          (nhds (((Real.goldenRatio⁻¹ : ℝ) ^ 3) / 2)) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        pom_max_fiber_achievers_hidden_bit_prob_spectrum_ratio_tendsto_inv_golden_cube.div_const 2
    have hhalf : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    simpa using hhalf.add hdelta

end Omega.POM
