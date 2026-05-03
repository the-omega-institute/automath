import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.MaxFiberAchieversHiddenBitImbalance

open Filter
open scoped Topology goldenRatio

namespace Omega.POM

/-- Paper label: `cor:pom-max-fiber-hidden-bit-bias-spectrum`. -/
theorem paper_pom_max_fiber_hidden_bit_bias_spectrum :
    Tendsto (fun k : ℕ => (Nat.fib (k + 1) : ℝ) / Nat.fib (k + 4)) atTop
        (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 3)) ∧
      Tendsto (fun k : ℕ => (Nat.fib k : ℝ) / Nat.fib (k + 3)) atTop
        (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 3)) ∧
      (Real.goldenRatio⁻¹ : ℝ) ^ 3 = Real.sqrt 5 - 2 := by
  have hcube :
      Tendsto (fun k : ℕ => (Nat.fib k : ℝ) / Nat.fib (k + 3)) atTop
        (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 3)) :=
    paper_pom_max_fiber_achievers_hidden_bit_imbalance.2.2
  refine ⟨?_, hcube, ?_⟩
  · have hshift := hcube.comp (tendsto_add_atTop_nat (1 : ℕ))
    simpa [Function.comp_def, Nat.add_assoc] using hshift
  · have hinv : (Real.goldenRatio⁻¹ : ℝ) = Real.goldenRatio - 1 := by
      have hinvψ : (Real.goldenRatio⁻¹ : ℝ) = -Real.goldenConj := by
        simpa [one_div] using Real.inv_goldenRatio
      nlinarith [hinvψ, Real.goldenRatio_add_goldenConj]
    have hphi_def : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := by
      rw [Real.goldenRatio]
    have hsqrt_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := by
      norm_num [Real.sq_sqrt]
    have hsqrt_cube : (Real.sqrt 5 : ℝ) ^ 3 = 5 * Real.sqrt 5 := by
      calc
        (Real.sqrt 5 : ℝ) ^ 3 = (Real.sqrt 5) ^ 2 * Real.sqrt 5 := by ring
        _ = 5 * Real.sqrt 5 := by rw [hsqrt_sq]
    rw [hinv, hphi_def]
    ring_nf
    nlinarith [hsqrt_sq, hsqrt_cube]

end Omega.POM
