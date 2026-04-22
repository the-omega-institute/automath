import Mathlib.Data.Fintype.Card
import Omega.POM.BbitOracleCapacityClosedForm

namespace Omega.Folding

open scoped BigOperators

/-- The `B`-bit oracle capacity is exactly the fiberwise sum of the truncated multiplicities.
    thm:fold-oracle-capacity-closed-form -/
theorem paper_fold_oracle_capacity_closed_form
    {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq Ω] [DecidableEq X] (fold : Ω → X) (B : Nat) :
    Omega.POM.bbitOracleCapacity fold B =
      ∑ x : X, Nat.min (Fintype.card {ω : Ω // fold ω = x}) (2 ^ B) := by
  simpa using Omega.POM.paper_pom_bbit_oracle_capacity_closed_form fold B

end Omega.Folding
