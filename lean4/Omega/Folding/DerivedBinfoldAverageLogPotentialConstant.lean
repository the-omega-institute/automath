import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.Entropy
import Omega.Folding.FoldBinTwoStateAsymptotic

open Filter

namespace Omega.Folding

/-- The explicit growth contribution in the two-state proxy for the average log potential. -/
noncomputable def derivedBinfoldAverageLogPotentialMainTerm : ℝ :=
  Real.log foldBinTwoStateGrowth

/-- The explicit constant isolated from the terminal-state density limit. -/
noncomputable def derivedBinfoldAverageLogPotentialConstantValue : ℝ :=
  -(((Real.goldenRatio⁻¹ : ℝ) ^ 2) * Real.log Real.goldenRatio)

/-- Concrete wrapper for the average-log-potential constant derivation: the two-state asymptotic
holds, the last-bit density has Fibonacci limit `φ⁻²`, and the constant is the advertised one. -/
def derivedBinfoldAverageLogPotentialConstant (D : FoldBinTwoStateAsymptoticData) : Prop :=
  D.uniform_two_state_asymptotic ∧
    Tendsto (fun m : ℕ => (Nat.fib m : ℝ) / Nat.fib (m + 2)) atTop
      (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 2)) ∧
    derivedBinfoldAverageLogPotentialMainTerm = Real.log (2 / Real.goldenRatio) ∧
    derivedBinfoldAverageLogPotentialConstantValue =
      -(((Real.goldenRatio⁻¹ : ℝ) ^ 2) * Real.log Real.goldenRatio)

private theorem fib_ratio_tendsto_inv_golden :
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / Nat.fib (n + 1)) atTop
      (nhds (Real.goldenRatio⁻¹)) := by
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

private theorem fib_ratio_tendsto_inv_golden_sq :
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / Nat.fib (n + 2)) atTop
      (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 2)) := by
  have hprod0 :
      Tendsto
        (fun n : ℕ =>
          ((Nat.fib n : ℝ) / Nat.fib (n + 1)) * ((Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)))
        atTop
        (nhds ((Real.goldenRatio⁻¹) * (Real.goldenRatio⁻¹))) := by
    simpa using fib_ratio_tendsto_inv_golden.mul fib_ratio_tendsto_inv_golden_shift
  have hprod :
      Tendsto
        (fun n : ℕ =>
          ((Nat.fib n : ℝ) / Nat.fib (n + 1)) * ((Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)))
        atTop
        (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 2)) := by
    simpa [pow_two] using hprod0
  refine Tendsto.congr' ?_ hprod
  filter_upwards [Filter.Eventually.of_forall fun _ => True.intro] with n _
  have hfib : (Nat.fib (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos n)))
  field_simp [hfib]

/-- Paper label: `thm:derived-binfold-average-log-potential-constant`. -/
theorem paper_derived_binfold_average_log_potential_constant (D : FoldBinTwoStateAsymptoticData) :
    derivedBinfoldAverageLogPotentialConstant D := by
  refine ⟨paper_fold_bin_two_state_asymptotic D, fib_ratio_tendsto_inv_golden_sq, ?_, ?_⟩
  · simp [derivedBinfoldAverageLogPotentialMainTerm, foldBinTwoStateGrowth]
  · rfl

end Omega.Folding
