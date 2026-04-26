import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinTwoStateAsymptotic

namespace Omega.Zeta

open Omega.Folding
open Omega.Folding.FoldBinTwoStateAsymptoticData

/-- The explicit cutoff supplied by the concrete two-state formulas. -/
def xi_time_part70ab_terminal_bit_eventual_strict_stratification_cutoff : ℕ := 0

/-- The terminal-bit layer value in the concrete two-state model. -/
noncomputable def xi_time_part70ab_terminal_bit_eventual_strict_stratification_layer_value
    (m : ℕ) (b : Bool) : ℝ :=
  foldBinTwoStateFiberCount m b

/-- Eventual strict separation of the two terminal-bit layers. -/
def xi_time_part70ab_terminal_bit_eventual_strict_stratification_statement
    (D : FoldBinTwoStateAsymptoticData) : Prop :=
  D.uniform_two_state_asymptotic ∧
    xi_time_part70ab_terminal_bit_eventual_strict_stratification_cutoff = 0 ∧
    ∀ m ≥ xi_time_part70ab_terminal_bit_eventual_strict_stratification_cutoff,
      xi_time_part70ab_terminal_bit_eventual_strict_stratification_layer_value m true <
        xi_time_part70ab_terminal_bit_eventual_strict_stratification_layer_value m false

/-- Paper label: `thm:xi-time-part70ab-terminal-bit-eventual-strict-stratification`. The exact
two-state formulas already force the `false` terminal-bit layer to sit strictly above the `true`
layer, so the eventual cutoff may be taken to be `0`. -/
theorem paper_xi_time_part70ab_terminal_bit_eventual_strict_stratification
    (D : Omega.Folding.FoldBinTwoStateAsymptoticData) :
    xi_time_part70ab_terminal_bit_eventual_strict_stratification_statement D := by
  have hD := paper_fold_bin_two_state_asymptotic D
  refine ⟨hD, rfl, ?_⟩
  intro m hm
  have hfalse := hD.2.1 m
  have htrue := hD.2.2 m
  have hinv_lt_one : (Real.goldenRatio⁻¹ : ℝ) < 1 := by
    simpa using inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hgrowth_nonneg : 0 ≤ foldBinTwoStateGrowth := by
    unfold foldBinTwoStateGrowth
    positivity
  have hpow_nonneg : 0 ≤ foldBinTwoStateGrowth ^ m := by
    exact pow_nonneg hgrowth_nonneg m
  rw [xi_time_part70ab_terminal_bit_eventual_strict_stratification_layer_value,
    xi_time_part70ab_terminal_bit_eventual_strict_stratification_layer_value, htrue, hfalse]
  nlinarith

end Omega.Zeta
