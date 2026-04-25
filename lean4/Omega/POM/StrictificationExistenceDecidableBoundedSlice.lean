import Mathlib.Data.Fintype.Basic

namespace Omega.POM

/-- Paper label: `cor:pom-strictification-existence-decidable-bounded-slice`. On a bounded
finite slice, the existence of an assignment satisfying all finite constraints is decidable.

This is a `def` rather than a `theorem` because `Decidable p` is data in `Type`, and Lean only
permits `theorem` declarations whose resulting type is a proposition. -/
def paper_pom_strictification_existence_decidable_bounded_slice
    {Sigma C : Type*} [Fintype Sigma] [Fintype C] (closes : Sigma → C → Prop)
    [∀ σ c, Decidable (closes σ c)] :
    Decidable (∃ σ : Sigma, ∀ c : C, closes σ c) := by
  infer_instance

end Omega.POM
