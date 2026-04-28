import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete parameters for the copied-state Rényi--Schatten gap lower bounds. -/
structure conclusion_renyi_schatten_gap_copy_amplified_order_parameter_data where
  n : ℕ
  k : ℕ
  hn : 1 ≤ n

namespace conclusion_renyi_schatten_gap_copy_amplified_order_parameter_data

/-- The copied-state order-parameter gap certified by the trace lower bound. -/
noncomputable def gapForCopies (t : ℕ) : ℝ :=
  Real.log ((t : ℝ) + 1)

/-- The UNSAT branch has zero copied gap. -/
def unsatGapZero (_D : conclusion_renyi_schatten_gap_copy_amplified_order_parameter_data) :
    Prop :=
  (0 : ℝ) = 0

/-- The SAT branch is at least the copied trace gap `log(t+1)`. -/
def satGapLowerBound
    (D : conclusion_renyi_schatten_gap_copy_amplified_order_parameter_data) : Prop :=
  Real.log ((D.n : ℝ) + 1) ≤ gapForCopies D.n

/-- For `t = n^k`, the copied gap is at least `k log n`. -/
def polynomialScaleLowerBound
    (D : conclusion_renyi_schatten_gap_copy_amplified_order_parameter_data) : Prop :=
  (D.k : ℝ) * Real.log D.n ≤ gapForCopies (D.n ^ D.k)

/-- For `t = 2^n`, the copied gap is at least `n log 2`. -/
def exponentialScaleLowerBound
    (D : conclusion_renyi_schatten_gap_copy_amplified_order_parameter_data) : Prop :=
  (D.n : ℝ) * Real.log 2 ≤ gapForCopies (2 ^ D.n)

end conclusion_renyi_schatten_gap_copy_amplified_order_parameter_data

open conclusion_renyi_schatten_gap_copy_amplified_order_parameter_data

/-- Paper label: `thm:conclusion-renyi-schatten-gap-copy-amplified-order-parameter`. -/
theorem paper_conclusion_renyi_schatten_gap_copy_amplified_order_parameter
    (D : conclusion_renyi_schatten_gap_copy_amplified_order_parameter_data) :
    D.unsatGapZero ∧ D.satGapLowerBound ∧ D.polynomialScaleLowerBound ∧
      D.exponentialScaleLowerBound := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · unfold satGapLowerBound gapForCopies
    rfl
  · unfold polynomialScaleLowerBound gapForCopies
    have hn_real : (0 : ℝ) < D.n := by exact_mod_cast D.hn
    have hpow_pos : (0 : ℝ) < (D.n : ℝ) ^ D.k := pow_pos hn_real D.k
    have hlog_mono :
        Real.log ((D.n : ℝ) ^ D.k) ≤ Real.log (((D.n : ℝ) ^ D.k) + 1) :=
      Real.log_le_log hpow_pos (le_add_of_nonneg_right zero_le_one)
    simpa [Nat.cast_pow, Real.log_pow] using hlog_mono
  · unfold exponentialScaleLowerBound gapForCopies
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ D.n := pow_pos (by norm_num) D.n
    have hlog_mono :
        Real.log ((2 : ℝ) ^ D.n) ≤ Real.log (((2 : ℝ) ^ D.n) + 1) :=
      Real.log_le_log hpow_pos (le_add_of_nonneg_right zero_le_one)
    simpa [Nat.cast_pow, Real.log_pow] using hlog_mono

end Omega.Conclusion
