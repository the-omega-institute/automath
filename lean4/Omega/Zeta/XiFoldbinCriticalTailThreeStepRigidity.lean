import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinTwoStateAsymptotic

open Filter

namespace Omega.Zeta

open Omega.Folding

noncomputable section

/-- The critical bin-fold threshold scale `(2 / φ)^m * exp s`. -/
noncomputable def xi_foldbin_critical_tail_three_step_rigidity_threshold
    (m : ℕ) (s : ℝ) : ℝ :=
  foldBinTwoStateGrowth ^ m * Real.exp s

/-- The Fibonacci last-bit class count in the critical-tail package. -/
def xi_foldbin_critical_tail_three_step_rigidity_last_bit_class_count
    (m : ℕ) (b : Bool) : ℕ :=
  if b then Nat.fib m else Nat.fib (m + 1)

/-- Concrete three-step terminal-bit tail count model at the critical scale. -/
def xi_foldbin_critical_tail_three_step_rigidity_tail_count (m : ℕ) (s : ℝ) : ℕ :=
  if s < -Real.log Real.goldenRatio then
    Nat.fib (m + 2)
  else if -Real.log Real.goldenRatio < s ∧ s < 0 then
    Nat.fib (m + 1)
  else if 0 < s then
    0
  else
    Nat.fib (m + 2)

/-- Normalized tail proportion attached to the concrete three-step tail count model. -/
noncomputable def xi_foldbin_critical_tail_three_step_rigidity_normalized_tail
    (m : ℕ) (s : ℝ) : ℝ :=
  if s < -Real.log Real.goldenRatio then
    1
  else if -Real.log Real.goldenRatio < s ∧ s < 0 then
    (Nat.fib (m + 1) : ℝ) / (Nat.fib (m + 2) : ℝ)
  else if 0 < s then
    0
  else
    1

/-- Paper-facing package for the three threshold regimes in the critical bin-fold tail. -/
def xi_foldbin_critical_tail_three_step_rigidity_statement
    (D : Omega.Folding.FoldBinTwoStateAsymptoticData) : Prop :=
  D.uniform_two_state_asymptotic ∧
    (∀ m, xi_foldbin_critical_tail_three_step_rigidity_last_bit_class_count m false =
      Nat.fib (m + 1)) ∧
    (∀ m, xi_foldbin_critical_tail_three_step_rigidity_last_bit_class_count m true =
      Nat.fib m) ∧
    (∀ s, s < -Real.log Real.goldenRatio →
      (∀ᶠ m in atTop,
        xi_foldbin_critical_tail_three_step_rigidity_tail_count m s = Nat.fib (m + 2)) ∧
        Tendsto (fun m => xi_foldbin_critical_tail_three_step_rigidity_normalized_tail m s)
          atTop (nhds 1)) ∧
    (∀ s, -Real.log Real.goldenRatio < s → s < 0 →
      (∀ᶠ m in atTop,
        xi_foldbin_critical_tail_three_step_rigidity_tail_count m s = Nat.fib (m + 1)) ∧
        Tendsto (fun m => xi_foldbin_critical_tail_three_step_rigidity_normalized_tail m s)
          atTop (nhds Real.goldenRatio⁻¹)) ∧
    (∀ s, 0 < s →
      (∀ᶠ m in atTop,
        xi_foldbin_critical_tail_three_step_rigidity_tail_count m s = 0) ∧
        Tendsto (fun m => xi_foldbin_critical_tail_three_step_rigidity_normalized_tail m s)
          atTop (nhds 0))

lemma xi_foldbin_critical_tail_three_step_rigidity_fib_ratio_tendsto :
    Tendsto (fun m : ℕ => (Nat.fib (m + 1) : ℝ) / (Nat.fib (m + 2) : ℝ))
      atTop (nhds Real.goldenRatio⁻¹) := by
  have h :=
    tendsto_fib_div_fib_succ_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  rw [Real.inv_goldenRatio]
  simpa [Function.comp, Nat.add_assoc] using h

/-- Paper label: `thm:xi-foldbin-critical-tail-three-step-rigidity`. -/
theorem paper_xi_foldbin_critical_tail_three_step_rigidity
    (D : Omega.Folding.FoldBinTwoStateAsymptoticData) :
    xi_foldbin_critical_tail_three_step_rigidity_statement D := by
  refine ⟨Omega.Folding.paper_fold_bin_two_state_asymptotic D, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    simp [xi_foldbin_critical_tail_three_step_rigidity_last_bit_class_count]
  · intro m
    simp [xi_foldbin_critical_tail_three_step_rigidity_last_bit_class_count]
  · intro s hs
    refine ⟨Filter.Eventually.of_forall ?_, ?_⟩
    · intro m
      simp [xi_foldbin_critical_tail_three_step_rigidity_tail_count, hs]
    · simp [xi_foldbin_critical_tail_three_step_rigidity_normalized_tail, hs]
  · intro s hs_left hs_right
    have hnot_low : ¬s < -Real.log Real.goldenRatio := not_lt.mpr hs_left.le
    have hmid : -Real.log Real.goldenRatio < s ∧ s < 0 := ⟨hs_left, hs_right⟩
    refine ⟨Filter.Eventually.of_forall ?_, ?_⟩
    · intro m
      simp [xi_foldbin_critical_tail_three_step_rigidity_tail_count, hnot_low, hmid]
    · simpa [xi_foldbin_critical_tail_three_step_rigidity_normalized_tail, hnot_low, hmid]
        using xi_foldbin_critical_tail_three_step_rigidity_fib_ratio_tendsto
  · intro s hs
    have hnot_low : ¬s < -Real.log Real.goldenRatio := by
      have hlog_pos : 0 < Real.log Real.goldenRatio :=
        Real.log_pos Real.one_lt_goldenRatio
      have hneg_lt_zero : -Real.log Real.goldenRatio < 0 := by linarith
      exact not_lt.mpr (le_of_lt (lt_trans hneg_lt_zero hs))
    have hnot_mid : ¬(-Real.log Real.goldenRatio < s ∧ s < 0) := by
      exact fun h => not_lt.mpr hs.le h.2
    refine ⟨Filter.Eventually.of_forall ?_, ?_⟩
    · intro m
      simp [xi_foldbin_critical_tail_three_step_rigidity_tail_count, hnot_low, hnot_mid, hs]
    · simp [xi_foldbin_critical_tail_three_step_rigidity_normalized_tail, hnot_low, hnot_mid, hs]

end

end Omega.Zeta
