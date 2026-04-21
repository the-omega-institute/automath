import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.POM.BbitOracleCapacityClosedForm

namespace Omega.Folding

open scoped BigOperators

/-- The binary-coded oracle capacity is bounded by the number of fibers times the `B`-bit budget.
    cor:fold-oracle-pigeonhole-bound -/
theorem paper_fold_oracle_pigeonhole_bound
    {A X : Type*} [Fintype A] [Fintype X] [DecidableEq A] [DecidableEq X] (f : A → X) (B : ℕ) :
    Omega.POM.bbitOracleCapacity f B ≤ Fintype.card X * 2 ^ B := by
  classical
  calc
    Omega.POM.bbitOracleCapacity f B
        = ∑ x : X, Nat.min (Fintype.card {a : A // f a = x}) (2 ^ B) := by
            simpa using Omega.POM.paper_pom_bbit_oracle_capacity_closed_form f B
    _ ≤ ∑ _x : X, 2 ^ B := by
          exact Finset.sum_le_sum (fun x _ => Nat.min_le_right (Fintype.card {a : A // f a = x}) (2 ^ B))
    _ = Fintype.card X * 2 ^ B := by
          simp

end Omega.Folding
