import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- Concrete finite wrapper for the two exact-inversion obstructions: the peak-fiber dyadic
threshold and the pigeonhole lower bound. The visible-state term is specialized to the Fibonacci
cardinality `|X_m| = F_{m+2}` in the statement. -/
structure fold_oracle_exact_inversion_joint_rate_lower_bound_data where
  bitBudget : ℕ → ℝ
  maxFiberMass : ℕ → ℕ
  visibleCard : ℕ → ℕ
  exactInversion_lower :
    ∀ m, (Nat.clog 2 (maxFiberMass m) : ℝ) ≤ bitBudget m
  pigeonhole_lower :
    ∀ m : ℕ, (m : ℝ) - Real.log (visibleCard m) / Real.log 2 ≤ bitBudget m
  visibleCard_fib :
    ∀ m, visibleCard m = Nat.fib (m + 2)

/-- Joint fixed-length lower bound obtained by taking the maximum of the two standard exact
inversion obstructions and specializing the visible-state count to `F_{m+2}`. -/
def fold_oracle_exact_inversion_joint_rate_lower_bound_statement
    (D : fold_oracle_exact_inversion_joint_rate_lower_bound_data) : Prop :=
  ∀ m : ℕ,
    max ((Nat.clog 2 (D.maxFiberMass m) : ℝ))
        ((m : ℝ) - Real.log (Nat.fib (m + 2)) / Real.log 2) ≤
      D.bitBudget m

/-- Paper label: `thm:fold-oracle-exact-inversion-joint-rate-lower-bound`. -/
theorem paper_fold_oracle_exact_inversion_joint_rate_lower_bound
    (D : fold_oracle_exact_inversion_joint_rate_lower_bound_data) :
    fold_oracle_exact_inversion_joint_rate_lower_bound_statement D := by
  intro m
  refine max_le_iff.mpr ?_
  refine ⟨D.exactInversion_lower m, ?_⟩
  simpa [D.visibleCard_fib m] using D.pigeonhole_lower m

end Omega.Folding
