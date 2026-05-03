import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Folding.FoldBinMaxFiberExponent
import Omega.Folding.OracleCapacityClosedForm

open Filter
open scoped BigOperators Topology

namespace Omega.Conclusion

noncomputable section

/-- The average bin-fold fiber size `2^m / F_{m+2}`. -/
def conclusion_foldgauge_local_extraction_budget_barrier_averageFiber (m : ℕ) : ℝ :=
  (2 : ℝ) ^ m / (Nat.fib (m + 2) : ℝ)

/-- The normalized `B`-bit oracle success bound obtained by dividing the closed form by `2^m`. -/
def conclusion_foldgauge_local_extraction_budget_barrier_oracleRate (m B : ℕ)
    (fold : Fin (2 ^ m) → Fin (Nat.fib (m + 2))) : ℝ :=
  (Omega.POM.bbitOracleCapacity fold B : ℝ) / (2 : ℝ) ^ m

/-- Concrete statement for the local-extraction budget barrier: the closed form is the fiberwise
truncated sum, the normalized success is bounded by `2^B / \bar d_m`, and the average-fiber
scale has the golden-ratio exponential rate. -/
def conclusion_foldgauge_local_extraction_budget_barrier_statement : Prop :=
  (∀ m B : ℕ, ∀ fold : Fin (2 ^ m) → Fin (Nat.fib (m + 2)),
      Omega.POM.bbitOracleCapacity fold B =
        ∑ x : Fin (Nat.fib (m + 2)),
          Nat.min (Fintype.card {ω : Fin (2 ^ m) // fold ω = x}) (2 ^ B)) ∧
    (∀ m B : ℕ, ∀ fold : Fin (2 ^ m) → Fin (Nat.fib (m + 2)),
      conclusion_foldgauge_local_extraction_budget_barrier_oracleRate m B fold ≤
        (2 : ℝ) ^ B / conclusion_foldgauge_local_extraction_budget_barrier_averageFiber m) ∧
      (∀ m : ℕ,
        conclusion_foldgauge_local_extraction_budget_barrier_averageFiber m =
          (2 : ℝ) ^ m / (Nat.fib (m + 2) : ℝ)) ∧
        Tendsto
          (fun m : ℕ =>
            Real.log (conclusion_foldgauge_local_extraction_budget_barrier_averageFiber m) / m)
          atTop (𝓝 (Real.log (2 / Real.goldenRatio)))

/-- Paper label: `thm:conclusion-foldgauge-local-extraction-budget-barrier`. -/
theorem paper_conclusion_foldgauge_local_extraction_budget_barrier :
    conclusion_foldgauge_local_extraction_budget_barrier_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m B fold
    exact Omega.Folding.paper_fold_oracle_capacity_closed_form fold B
  · intro m B fold
    have hclosed := Omega.Folding.paper_fold_oracle_capacity_closed_form fold B
    have hsum_bound :
        (∑ x : Fin (Nat.fib (m + 2)),
            (Nat.min (Fintype.card {ω : Fin (2 ^ m) // fold ω = x}) (2 ^ B) : ℝ)) ≤
          (Nat.fib (m + 2) : ℝ) * (2 : ℝ) ^ B := by
      calc
        (∑ x : Fin (Nat.fib (m + 2)),
            (Nat.min (Fintype.card {ω : Fin (2 ^ m) // fold ω = x}) (2 ^ B) : ℝ)) ≤
            ∑ _x : Fin (Nat.fib (m + 2)), ((2 ^ B : ℕ) : ℝ) := by
              refine Finset.sum_le_sum ?_
              intro x _hx
              exact_mod_cast
                (Nat.min_le_right
                  (Fintype.card {ω : Fin (2 ^ m) // fold ω = x}) (2 ^ B))
        _ = (Nat.fib (m + 2) : ℝ) * (2 : ℝ) ^ B := by
              simp [Nat.cast_pow]
    have hpow_pos : 0 < (2 : ℝ) ^ m := by positivity
    have hfib_pos : 0 < (Nat.fib (m + 2) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < m + 2)
    have hrate :
        conclusion_foldgauge_local_extraction_budget_barrier_oracleRate m B fold =
          (∑ x : Fin (Nat.fib (m + 2)),
            (Nat.min (Fintype.card {ω : Fin (2 ^ m) // fold ω = x}) (2 ^ B) : ℝ)) /
            (2 : ℝ) ^ m := by
      unfold conclusion_foldgauge_local_extraction_budget_barrier_oracleRate
      rw [hclosed]
      norm_num
    rw [hrate]
    calc
      (∑ x : Fin (Nat.fib (m + 2)),
          (Nat.min (Fintype.card {ω : Fin (2 ^ m) // fold ω = x}) (2 ^ B) : ℝ)) /
          (2 : ℝ) ^ m ≤
          ((Nat.fib (m + 2) : ℝ) * (2 : ℝ) ^ B) / (2 : ℝ) ^ m := by
            exact div_le_div_of_nonneg_right hsum_bound (le_of_lt hpow_pos)
      _ = (2 : ℝ) ^ B /
          conclusion_foldgauge_local_extraction_budget_barrier_averageFiber m := by
            unfold conclusion_foldgauge_local_extraction_budget_barrier_averageFiber
            field_simp [ne_of_gt hpow_pos, ne_of_gt hfib_pos]
  · intro m
    rfl
  · simpa [conclusion_foldgauge_local_extraction_budget_barrier_averageFiber] using
      Omega.paper_fold_bin_max_fiber_exponent.2

end

end Omega.Conclusion
