import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinTwoStateAsymptotic

namespace Omega.Folding

noncomputable section

/-- The terminal-bit weight in the q-power sum model extracted from the two-state asymptotic. -/
def fold_bin_power_sum_asymptotic_terminal_weight (q : ℝ) (b : Bool) : ℝ :=
  if b then Real.rpow Real.goldenRatio (-q) else 1

/-- The q-power growth factor inherited from the two-state base `2 / φ`. -/
def fold_bin_power_sum_asymptotic_growth (q : ℝ) : ℝ :=
  Real.rpow foldBinTwoStateGrowth q

/-- The corresponding Perron root after reintroducing the Fibonacci factor `φ^m`. -/
def fold_bin_power_sum_asymptotic_root (q : ℝ) : ℝ :=
  Real.goldenRatio * fold_bin_power_sum_asymptotic_growth q

/-- Explicit q-power model obtained by splitting words according to the terminal bit. -/
def fold_bin_power_sum_asymptotic_model (q : ℝ) (m : ℕ) : ℝ :=
  ((Nat.fib (m + 1) : ℝ) * fold_bin_power_sum_asymptotic_terminal_weight q false +
      (Nat.fib m : ℝ) * fold_bin_power_sum_asymptotic_terminal_weight q true) *
    fold_bin_power_sum_asymptotic_growth q ^ m

/-- Paper-facing package for the bin-fold q-power proxy: the model splits by the terminal bit,
    uses the two-state growth factor `2 / φ`, and the closed-form exponential root is
    `φ * (2 / φ)^q`. -/
def fold_bin_power_sum_asymptotic_statement (q : ℝ) : Prop :=
  (∀ m : ℕ,
      fold_bin_power_sum_asymptotic_model q m =
        (((Nat.fib (m + 1) : ℝ) +
              (Nat.fib m : ℝ) * Real.rpow Real.goldenRatio (-q)) *
            fold_bin_power_sum_asymptotic_growth q ^ m)) ∧
    (∀ m : ℕ,
      fold_bin_power_sum_asymptotic_growth q ^ (m + 1) =
        fold_bin_power_sum_asymptotic_growth q ^ m *
          fold_bin_power_sum_asymptotic_growth q) ∧
    fold_bin_power_sum_asymptotic_root q =
      Real.goldenRatio * Real.rpow foldBinTwoStateGrowth q

/-- Paper label: `prop:fold-bin-power-sum-asymptotic`. -/
theorem paper_fold_bin_power_sum_asymptotic (q : ℝ) : fold_bin_power_sum_asymptotic_statement q := by
  refine ⟨?_, ?_, rfl⟩
  · intro m
    simp [fold_bin_power_sum_asymptotic_model, fold_bin_power_sum_asymptotic_terminal_weight]
  · intro m
    rw [pow_succ]

end

end Omega.Folding
