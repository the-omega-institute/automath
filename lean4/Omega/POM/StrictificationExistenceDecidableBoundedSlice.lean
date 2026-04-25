import Mathlib.Data.Fintype.Basic

namespace Omega.POM

/-- Paper label: `cor:pom-strictification-existence-decidable-bounded-slice`. On a bounded
finite slice, the existence of an assignment satisfying all finite constraints is decidable.

This is a `def` rather than a `theorem` because `Decidable p` is data in `Type`, and Lean only
permits `theorem` declarations whose resulting type is a proposition. -/
def paper_pom_strictification_existence_decidable_bounded_slice
    (Constraint Assignment : Type*) [Fintype Constraint] [Fintype Assignment]
    (satisfies : Assignment → Constraint → Prop)
    [∀ a c, Decidable (satisfies a c)] :
    Decidable (∃ a : Assignment, ∀ c : Constraint, satisfies a c) := by
  infer_instance

end Omega.POM
