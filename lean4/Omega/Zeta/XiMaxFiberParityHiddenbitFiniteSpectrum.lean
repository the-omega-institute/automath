import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Tactic
import Omega.POM.MaxFiberHiddenBitBiasSpectrum

open Filter
open scoped Topology goldenRatio

namespace Omega.Zeta

/-- Paper label: `cor:xi-max-fiber-parity-hiddenbit-finite-spectrum`. -/
theorem paper_xi_max_fiber_parity_hiddenbit_finite_spectrum (k : ℕ) (p1 : ℝ)
    (hp1 :
      p1 = 1 / 2 ∨
        p1 = 1 / 2 + (Nat.fib (k - 2) : ℝ) / (2 * Nat.fib (k + 1)) ∨
          p1 = 1 / 2 - (Nat.fib (k - 2) : ℝ) / (2 * Nat.fib (k + 1))) :
    let Δk : ℝ := (Nat.fib (k - 2) : ℝ) / (2 * Nat.fib (k + 1));
    (p1 = 1 / 2 ∨ p1 = 1 / 2 + Δk ∨ p1 = 1 / 2 - Δk) ∧
      Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / (2 * Nat.fib (n + 3))) atTop
        (nhds ((1 / 2 : ℝ) * (Real.goldenRatio⁻¹) ^ 3)) := by
  dsimp
  refine ⟨hp1, ?_⟩
  have hcube :
      Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / Nat.fib (n + 3)) atTop
        (nhds ((Real.goldenRatio⁻¹ : ℝ) ^ 3)) :=
    Omega.POM.paper_pom_max_fiber_hidden_bit_bias_spectrum.2.1
  have hhalf :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ((Nat.fib n : ℝ) / Nat.fib (n + 3)))
        atTop (nhds ((1 / 2 : ℝ) * (Real.goldenRatio⁻¹) ^ 3)) :=
    hcube.const_mul (1 / 2 : ℝ)
  refine hhalf.congr' ?_
  filter_upwards [Filter.Eventually.of_forall
    (fun n : ℕ =>
      show (Nat.fib (n + 3) : ℝ) ≠ 0 by
        exact_mod_cast (ne_of_gt (Nat.fib_pos.2 (by omega : 0 < n + 3))))] with n hn
  field_simp [hn]

end Omega.Zeta
