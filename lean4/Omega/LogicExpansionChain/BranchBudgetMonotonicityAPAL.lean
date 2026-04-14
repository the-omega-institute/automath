import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log

namespace Omega.LogicExpansionChain

set_option maxHeartbeats 400000 in
/-- Publication-facing corollary: once refinement does not increase the hidden branch kernel
    cardinality, its base-`2` bit budget cannot increase either.
    cor:branch-budget-monotonicity -/
theorem paper_conservative_extension_branch_budget_monotonicity_apal
    {kw kv : Type*} (ikw : Fintype kw) (ikv : Fintype kv)
    (hcard : @Fintype.card kw ikw ≤ @Fintype.card kv ikv) :
    Nat.log 2 (@Fintype.card kw ikw) ≤ Nat.log 2 (@Fintype.card kv ikv) :=
  Nat.log_mono_right hcard

end Omega.LogicExpansionChain
