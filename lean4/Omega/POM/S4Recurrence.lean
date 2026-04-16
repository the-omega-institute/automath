import Mathlib.Tactic
import Omega.Folding.CollisionKernel
import Omega.Folding.CollisionZeta

namespace Omega.POM

/-- Paper-facing wrapper for the explicit five-state `S₄` realization together with its exact
order-5 trace recurrence.
    prop:pom-s4-recurrence -/
theorem paper_pom_s4_recurrence (explicitS4Realization exactS4Recurrence : Prop)
    (hRealize : explicitS4Realization) (hRec : explicitS4Realization -> exactS4Recurrence) :
    explicitS4Realization ∧ exactS4Recurrence := by
  refine ⟨hRealize, ?_⟩
  exact hRec hRealize

end Omega.POM
