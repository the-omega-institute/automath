import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.Entropy

open Filter
open scoped goldenRatio

namespace Omega.Conclusion

private theorem fib_ratio_tendsto_inv_golden :
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / Nat.fib (n + 1)) atTop (nhds (Real.goldenRatio⁻¹)) := by
  have hinv :
      Tendsto (fun n : ℕ => (((Nat.fib (n + 1) : ℝ) / Nat.fib n)⁻¹)) atTop
        (nhds (Real.goldenRatio⁻¹)) := by
    simpa using Omega.Entropy.fib_ratio_tendsto.inv₀ Real.goldenRatio_ne_zero
  refine Tendsto.congr' ?_ hinv
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hfib : (Nat.fib n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr hn))
  field_simp [hfib]

private theorem fib_ratio_tendsto_inv_golden_shift :
    Tendsto (fun n : ℕ => (Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
  have hinv :
      Tendsto (fun n : ℕ => (((Nat.fib (n + 2) : ℝ) / Nat.fib (n + 1))⁻¹)) atTop
        (nhds (Real.goldenRatio⁻¹)) := by
    simpa using Omega.Entropy.fib_ratio_tendsto_golden.inv₀ Real.goldenRatio_ne_zero
  refine Tendsto.congr' ?_ hinv
  filter_upwards [Filter.Eventually.of_forall fun n => Nat.fib_pos.mpr (Nat.succ_pos _)] with n hn
  have hfib : (Nat.fib (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hfib]

private theorem fib_ratio_tendsto_inv_golden_shift_shift :
    Tendsto (fun n : ℕ => (Nat.fib (n + 2) : ℝ) / Nat.fib (n + 3)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
  simpa [Nat.add_assoc] using
    fib_ratio_tendsto_inv_golden_shift.comp (tendsto_add_atTop_nat 1)

private theorem fib_ratio_tendsto_inv_golden_cubed :
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / Nat.fib (n + 3)) atTop
      (nhds ((Real.goldenRatio⁻¹) ^ 3)) := by
  have hprod0 :
      Tendsto
        (fun n : ℕ =>
          ((Nat.fib n : ℝ) / Nat.fib (n + 1)) *
            ((Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) *
              ((Nat.fib (n + 2) : ℝ) / Nat.fib (n + 3)))
        atTop
        (nhds ((Real.goldenRatio⁻¹) * (Real.goldenRatio⁻¹) * (Real.goldenRatio⁻¹))) := by
    simpa [mul_assoc] using
      fib_ratio_tendsto_inv_golden.mul
        (fib_ratio_tendsto_inv_golden_shift.mul fib_ratio_tendsto_inv_golden_shift_shift)
  have hprod :
      Tendsto
        (fun n : ℕ =>
          ((Nat.fib n : ℝ) / Nat.fib (n + 1)) *
            ((Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) *
              ((Nat.fib (n + 2) : ℝ) / Nat.fib (n + 3)))
        atTop
        (nhds ((Real.goldenRatio⁻¹) ^ 3)) := by
    simpa [pow_succ, mul_assoc] using hprod0
  refine Tendsto.congr' ?_ hprod
  · filter_upwards [Filter.Eventually.of_forall fun _ => True.intro] with n _
    have hfib1 : (Nat.fib (n + 1) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos n)))
    have hfib2 : (Nat.fib (n + 2) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos (n + 1))))
    field_simp [hfib1, hfib2]

private theorem fib_hiddenbit_delta_tendsto :
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / (2 * Nat.fib (n + 3))) atTop
      (nhds ((1 / 2 : ℝ) * (Real.goldenRatio⁻¹) ^ 3)) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    Filter.Tendsto.const_mul (1 / 2 : ℝ) fib_ratio_tendsto_inv_golden_cubed

private theorem golden_inv_eq_half_plus_half_inv_cube :
    Real.goldenRatio⁻¹ = (1 / 2 : ℝ) + (1 / 2 : ℝ) * (Real.goldenRatio⁻¹) ^ 3 := by
  have hsq := Omega.Entropy.goldenAngle_sq
  have hsq' : (Real.goldenRatio⁻¹ : ℝ) ^ 2 = 1 - Real.goldenRatio⁻¹ := by
    simpa [Omega.Entropy.goldenAngle] using hsq
  have hcube : (Real.goldenRatio⁻¹ : ℝ) ^ 3 = 2 * Real.goldenRatio⁻¹ - 1 := by
    calc
      (Real.goldenRatio⁻¹ : ℝ) ^ 3 = Real.goldenRatio⁻¹ * ((Real.goldenRatio⁻¹ : ℝ) ^ 2) := by
        ring
      _ = Real.goldenRatio⁻¹ * (1 - Real.goldenRatio⁻¹) := by rw [hsq']
      _ = 2 * Real.goldenRatio⁻¹ - 1 := by nlinarith [hsq']
  rw [hcube]
  ring

private theorem golden_inv_sq_eq_half_minus_half_inv_cube :
    (Real.goldenRatio⁻¹ : ℝ) ^ 2 = (1 / 2 : ℝ) - (1 / 2 : ℝ) * (Real.goldenRatio⁻¹) ^ 3 := by
  have hsq := Omega.Entropy.goldenAngle_sq
  have hsq' : (Real.goldenRatio⁻¹ : ℝ) ^ 2 = 1 - Real.goldenRatio⁻¹ := by
    simpa [Omega.Entropy.goldenAngle] using hsq
  have hcube : (Real.goldenRatio⁻¹ : ℝ) ^ 3 = 2 * Real.goldenRatio⁻¹ - 1 := by
    calc
      (Real.goldenRatio⁻¹ : ℝ) ^ 3 = Real.goldenRatio⁻¹ * ((Real.goldenRatio⁻¹ : ℝ) ^ 2) := by
        ring
      _ = Real.goldenRatio⁻¹ * (1 - Real.goldenRatio⁻¹) := by rw [hsq']
      _ = 2 * Real.goldenRatio⁻¹ - 1 := by nlinarith [hsq']
  rw [hcube]
  nlinarith [hsq']

/-- Conclusion-facing package for the odd-window maxfiber hidden-bit tristate crystal: the three
  values are recentered using `Δₖ`, the offset converges to `(1/2)φ^{-3}`, and the two
  noncentral states freeze to `φ^{-2}` and `φ^{-1}`.
    thm:conclusion-odd-maxfiber-hiddenbit-tristate-crystal -/
theorem paper_conclusion_odd_maxfiber_hiddenbit_tristate_crystal
    (k : ℕ) (p1 : ℝ)
    (hp1 : p1 = 1 / 2 ∨
      p1 = 1 / 2 + (Nat.fib (k - 2) : ℝ) / (2 * Nat.fib (k + 1)) ∨
        p1 = 1 / 2 - (Nat.fib (k - 2) : ℝ) / (2 * Nat.fib (k + 1))) :
    let Δk : ℝ := (Nat.fib (k - 2) : ℝ) / (2 * Nat.fib (k + 1))
    (p1 = 1 / 2 ∨ p1 = 1 / 2 + Δk ∨ p1 = 1 / 2 - Δk) ∧
      Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / (2 * Nat.fib (n + 3))) atTop
        (nhds ((1 / 2 : ℝ) * (Real.goldenRatio⁻¹) ^ 3)) ∧
      ((1 / 2 : ℝ) + (1 / 2 : ℝ) * (Real.goldenRatio⁻¹) ^ 3 = Real.goldenRatio⁻¹) ∧
      ((1 / 2 : ℝ) - (1 / 2 : ℝ) * (Real.goldenRatio⁻¹) ^ 3 =
        (Real.goldenRatio⁻¹ : ℝ) ^ 2) := by
  dsimp
  exact ⟨hp1, fib_hiddenbit_delta_tendsto, golden_inv_eq_half_plus_half_inv_cube.symm,
    golden_inv_sq_eq_half_minus_half_inv_cube.symm⟩

end Omega.Conclusion
