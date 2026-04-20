import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldBinTwoStateAsymptotic

namespace Omega.Folding

/-- Critical bin-fold oracle scale singled out by the two-state asymptotic. -/
noncomputable def foldBinOracleCriticalBase : ℝ :=
  foldBinTwoStateGrowth

/-- Continuous oracle capacity obtained by capping each of the `|X_m| = F_{m+2}` fibers at a
common budget. -/
noncomputable def foldBinOracleCapacity (m : ℕ) (budget : ℝ) : ℝ :=
  (Nat.fib (m + 2) : ℝ) * min budget (foldBinOracleCriticalBase ^ m)

/-- Success rate normalized by the saturated capacity. -/
noncomputable def foldBinOracleSuccess (m : ℕ) (budget : ℝ) : ℝ :=
  foldBinOracleCapacity m budget / ((Nat.fib (m + 2) : ℝ) * foldBinOracleCriticalBase ^ m)

lemma foldBinOracleCriticalBase_pos : 0 < foldBinOracleCriticalBase := by
  dsimp [foldBinOracleCriticalBase, foldBinTwoStateGrowth]
  positivity

lemma foldBinOracleSuccess_reduction (m : ℕ) (budget : ℝ) :
    foldBinOracleSuccess m budget =
      min budget (foldBinOracleCriticalBase ^ m) / (foldBinOracleCriticalBase ^ m) := by
  unfold foldBinOracleSuccess foldBinOracleCapacity
  have hfib_ne : (Nat.fib (m + 2) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.mpr (by omega)))
  have hcrit_ne : foldBinOracleCriticalBase ^ m ≠ 0 := by
    exact ne_of_gt (pow_pos foldBinOracleCriticalBase_pos _)
  field_simp [hfib_ne, hcrit_ne]

lemma foldBinOracleSuccess_above_threshold
    {a : ℝ} (ha : foldBinOracleCriticalBase < a) {m : ℕ} (_hm : 1 ≤ m) :
    foldBinOracleSuccess m (a ^ m) = 1 := by
  rw [foldBinOracleSuccess_reduction]
  have hbase_nonneg : 0 ≤ foldBinOracleCriticalBase := le_of_lt foldBinOracleCriticalBase_pos
  have hpow_le : foldBinOracleCriticalBase ^ m ≤ a ^ m := by
    exact pow_le_pow_left₀ hbase_nonneg (le_of_lt ha) m
  rw [min_eq_right hpow_le]
  have hpow_ne : foldBinOracleCriticalBase ^ m ≠ 0 := by
    exact ne_of_gt (pow_pos foldBinOracleCriticalBase_pos _)
  field_simp [hpow_ne]

lemma foldBinOracleSuccess_below_threshold_log
    {a : ℝ} (ha0 : 0 < a) (ha : a < foldBinOracleCriticalBase) {m : ℕ} (hm : 1 ≤ m) :
    Real.log (foldBinOracleSuccess m (a ^ m)) / m =
      Real.log a - Real.log foldBinOracleCriticalBase := by
  rw [foldBinOracleSuccess_reduction]
  have hpow_le : a ^ m ≤ foldBinOracleCriticalBase ^ m := by
    exact pow_le_pow_left₀ (le_of_lt ha0) (le_of_lt ha) m
  rw [min_eq_left hpow_le]
  have hapow_pos : 0 < a ^ m := pow_pos ha0 _
  have hcrit_pow_pos : 0 < foldBinOracleCriticalBase ^ m := pow_pos foldBinOracleCriticalBase_pos _
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [Real.log_div (ne_of_gt hapow_pos) (ne_of_gt hcrit_pow_pos), Real.log_pow, Real.log_pow]
  field_simp [hm_ne]

/-- Paper-facing oracle threshold package for the bin-fold toy capacity model: exact reduction to
the capped one-fiber ratio, saturation once the linear budget base dominates `2 / φ`, and the
subcritical logarithmic decay exponent. `thm:fold-bin-oracle-linear-threshold-exponent` -/
theorem paper_fold_bin_oracle_linear_threshold_exponent :
    (∀ m : ℕ, ∀ budget : ℝ,
      foldBinOracleSuccess m budget =
        min budget (foldBinOracleCriticalBase ^ m) / (foldBinOracleCriticalBase ^ m)) ∧
      (∀ a : ℝ, foldBinOracleCriticalBase < a →
        ∀ m : ℕ, 1 ≤ m → foldBinOracleSuccess m (a ^ m) = 1) ∧
      (∀ a : ℝ, 0 < a → a < foldBinOracleCriticalBase →
        ∀ m : ℕ, 1 ≤ m →
          Real.log (foldBinOracleSuccess m (a ^ m)) / m =
            Real.log a - Real.log foldBinOracleCriticalBase) := by
  refine ⟨foldBinOracleSuccess_reduction, ?_, ?_⟩
  · intro a ha m hm
    exact foldBinOracleSuccess_above_threshold ha hm
  · intro a ha0 ha m hm
    exact foldBinOracleSuccess_below_threshold_log ha0 ha hm

end Omega.Folding
